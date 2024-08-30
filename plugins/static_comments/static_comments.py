from __future__ import unicode_literals, print_function, absolute_import

from nikola.plugin_categories import SignalHandler
from nikola import utils
from nikola import metadata_extractors

import blinker
import hashlib
import io
import os

__all__ = []

_LOGGER = utils.get_logger('static_comments')


class Comment(object):
    """Represents a comment for a post, story or gallery."""

    # set by constructor
    id = None
    parent_id = None

    # set by creator
    content = ''  # should be a properly escaped HTML fragment
    author = None
    author_email = None  # should not be published by default
    author_url = None
    author_ip = None  # should not be published by default
    date_utc = None  # should be set via set_utc_date()
    date_localized = None  # should be set via set_utc_date()

    # set by _process_comments():
    indent_levels = None  # use for formatting comments as tree
    indent_change_before = 0  # use for formatting comments as tree
    indent_change_after = 0  # use for formatting comments as tree

    # The meaning of indent_levels, indent_change_before and
    # indent_change_after are the same as the values in utils.TreeNode.

    def __init__(self, site, owner, id, parent_id=None):
        """Initialize comment.

        site: Nikola site object;
        owner: post which 'owns' this comment;
        id: ID of comment;
        parent_id: ID of comment's parent, or None if it has none.
        """
        self._owner = owner
        self._config = site.config
        self.id = id
        self.parent_id = parent_id

    def set_utc_date(self, date_utc):
        """Set the date (in UTC). Automatically updates the localized date."""
        self.date_utc = utils.to_datetime(date_utc)
        self.date_localized = utils.to_datetime(date_utc, self._config['__tzinfo__'])

    def formatted_date(self, date_format):
        """Return the formatted localized date."""
        return utils.LocaleBorg().formatted_date(date_format, self.date_localized)

    def hash_values(self):
        """Return tuple of values whose hash to consider for computing the hash of this comment."""
        return (self.id, self.parent_id, self.content, self.author, self.author_url, self.date_utc)

    def __repr__(self):
        """Returns string representation for comment."""
        return '<Comment: {0} for {1}; indent: {2}>'.format(self.id, self._owner, self.indent_levels)


class StaticComments(SignalHandler):
    """Add static comments to posts."""

    def _compile_content(self, compiler_name, content, filename):
        """Compile comment content with specified page compiler."""
        if compiler_name == 'html':
            # Special case: just pass-through content.
            return content
        if compiler_name not in self.site.compilers:
            _LOGGER.error("Cannot find page compiler '{0}' for comment {1}!".format(compiler_name, filename))
            exit(1)
        compiler = self.site.compilers[compiler_name]
        try:
            result = compiler.compile_string(content, source_path=filename, is_two_file=True, lang=self.site.default_lang)
            if compiler_name == 'rest' and result[1] >= 3:
                # The reStructured Text page compiler returns error_level as second return value
                _LOGGER.error("reStructuredText page compiler ({0}) failed to compile comment {1}!".format(compiler_name, filename))
                exit(1)
            return result[0]
        except (AttributeError, NotImplementedError):
            try:
                return compiler.compile_to_string(content)
            except AttributeError:
                _LOGGER.error("Page compiler plugin '{0}' provides no compile_string or compile_to_string function (comment {1})!".format(compiler_name, filename))
                exit(1)

    def _parse_comment(self, filename):
        """Read a comment from a file, and return metadata dict and content."""
        with io.open(filename, "r", encoding="utf-8-sig") as f:
            source_text = f.read()

        meta = None
        content = None
        for priority in metadata_extractors.MetaPriority:
            found_in_priority = False
            for extractor in self.site.metadata_extractors_by['priority'].get(priority, []):
                # Call metadata_extractors.check_conditions to check whether the extractor
                # can be used, and if that succeeds, check whether all requirements for the
                # extractor are there. We pass None as the post since we don't have a post.
                # The (currently only) consequence is that compiler-specific plugins don't
                # work: after all, the compiler is determined from the metadata to be extracted.
                if not metadata_extractors.check_conditions(None, filename, extractor.conditions, self.site.config, source_text):
                    continue
                extractor.check_requirements()
                # Use the extractor to split the post into metadata and content, and to
                # decode the metadata.
                meta_str, content = extractor.split_metadata_from_text(source_text)
                new_meta = extractor._extract_metadata_from_text(meta_str)
                if new_meta:
                    found_in_priority = True
                    meta = new_meta
                    break

            if found_in_priority:
                break

        if meta is None:
            _LOGGER.error("Cannot identify metadata format for comment {0}!".format(filename))
            exit(1)
        return meta, content

    def _read_comment(self, filename, owner, id):
        """Read a comment from a file."""
        meta, content = self._parse_comment(filename)
        # create comment object
        comment = Comment(self.site, owner, id)
        # parse headers
        compiler_name = None
        for header, value in meta.items():
            if header == 'id':
                comment.id = value
            elif header == 'status':
                pass
            elif header == 'approved':
                if value != 'True':
                    return None
            elif header == 'author':
                comment.author = value
            elif header == 'authors':
                comment.author = value
            elif header == 'author_email':
                comment.author_email = value
            elif header == 'author_url':
                comment.author_url = value
            elif header == 'author_IP':
                comment.author_ip = value
            elif header == 'date_utc':
                comment.set_utc_date(value)
            elif header == 'parent_id':
                if value != 'None':
                    comment.parent_id = value
            elif header == 'wordpress_user_id':
                pass
            elif header == 'post_language':
                pass
            elif header == 'compiler':
                compiler_name = value
            elif header == 'slug':
                comment.slug = value
            elif header == 'title':
                comment.title = value
            elif header == 'date':
                comment.set_utc_date(value)
            elif header == 'in-reply-to':
                comment.parent_id = value
            else:
                _LOGGER.error("Unknown comment header: '{0}' (in file {1})".format(header, filename))
                exit(1)
        if compiler_name is None:
            # Try to read an html file next to the filename
            html = '.'.join([filename.rsplit('.', 1)[0], 'html'])
            if os.path.exists(html):
                with open(html) as fid:
                    comment.content = fid.read()
            else:
                _LOGGER.warn("Comment file '{0}' doesn't specify compiler! Using default 'wordpress'.".format(filename))
                compiler_name = 'wordpress'
                comment.content = self._compile_content(compiler_name, content, filename)
        else:
            # compile content
            comment.content = self._compile_content(compiler_name, content, filename)
        return comment

    def _scan_comments(self, path, file, owner):
        """Scan comments for post."""
        comments = {}
        try:
            post_base, post_id = file.rsplit('-', 1)
        except:
            # not a post, no comments
            return []
        if 'comment' in file:
            return []
        for dirpath, dirnames, filenames in os.walk(path, followlinks=True):
            if dirpath != path:
                continue
            for filename in filenames:
                if not ('comment' in filename and filename[0] == '.'):
                    continue
                # make sure this is a comment to "file"
                if not filename[1:].startswith(post_base + '-comment'):
                    continue
                # There is both a *.meta and a *.html. Send only the base of
                # the *.meta for parsing
                parts = filename.rsplit('.', 1)
                if parts[1] != 'meta':
                    continue
                # pull off the id
                parts = parts[0].rsplit('-', 1)
                try:
                    comment = self._read_comment(os.path.join(dirpath, filename), owner, parts[1])
                    if comment is not None:
                        # _LOGGER.info("Found comment '{0}' with ID {1}".format(os.path.join(dirpath, filename), comment.id))
                        comments[comment.id] = comment
                except ValueError as e:
                    _LOGGER.warn("Exception '{1}' while reading file '{0}'!".format(os.path.join(dirpath, filename), e))
                    pass
        return sorted(list(comments.values()), key=lambda c: c.date_utc)

    def _hash_post_comments(self, post):
        """Compute hash of all comments for this post."""
        # compute hash of comments
        hash = hashlib.md5()
        c = 0
        for comment in post.comments:
            c += 1
            for part in comment.hash_values():
                hash.update(str(part).encode('utf-8'))
        return hash.hexdigest()

    def _process_comments(self, comments):
        """Given a list of comments, rearranges them according to hierarchy and returns ordered list with indentation information."""
        # First, build tree structure out of TreeNode with comments attached
        root_list = []
        comment_nodes = dict()
        for comment in comments:
            node = utils.TreeNode(comment.id)
            node.comment = comment
            comment_nodes[comment.id] = node
        for comment in comments:
            node = comment_nodes[comment.id]
            parent_node = comment_nodes.get(node.comment.parent_id)
            if parent_node is not None:
                parent_node.children.append(node)
            else:
                root_list.append(node)
        # Then flatten structure and add indent information
        comment_nodes = utils.flatten_tree_structure(root_list)
        for node in comment_nodes:
            comment = node.comment
            comment.indent_levels = node.indent_levels
            comment.indent_change_before = node.indent_change_before
            comment.indent_change_after = node.indent_change_after
        return [node.comment for node in comment_nodes]

    def _process_post_object(self, post):
        """Add comments to a post object."""
        # Get all comments
        path, ext = os.path.splitext(post.source_path)
        path, file = os.path.split(path)
        comments = self._scan_comments(path, file, post)
        # Add ordered comment list to post
        post.comments = self._process_comments(comments)
        # Add dependency to post
        digest = self._hash_post_comments(post)
        post.add_dependency_uptodate(utils.config_changed({1: digest}, 'nikola.plugins.comments.static_comments:' + post.base_path), is_callable=False, add='page')
        return comments

    def _process_posts_and_pages(self, site):
        """Add comments to all posts."""
        if site is self.site:
            comments = []
            for post in site.timeline:
                comments += self._process_post_object(post)

    def set_site(self, site):
        """Set Nikola site object."""
        super(StaticComments, self).set_site(site)
        site._GLOBAL_CONTEXT['site_has_static_comments'] = True
        blinker.signal("scanned").connect(self._process_posts_and_pages)
