#!/usr/bin/python3
"""
VERY hackish script to find all the pypy blog posts which were in the front
page of HN on the day they were published.

Beware, after ~40-50 requests HN blacklists your IP
"""

import re
from dataclasses import dataclass
import py
import requests
from bs4 import BeautifulSoup

CACHE = py.path.local('/tmp/hn-cache')
CACHE.ensure(dir=1)

@dataclass
class HNArticle:
    points: int
    title: str
    href: str

@dataclass
class PyPyLink:
    rank: int
    points: int
    date: str
    title: str
    link: str

def download_maybe(key, url):
    cached = CACHE.join(key + '.html')
    if cached.exists():
        print('CACHED:', url)
        return cached.read()
    print('DOWNLOADING:', url)
    resp = requests.get(url)
    resp.raise_for_status()
    cached.write(resp.text)
    return resp.text

def download_hn_front_page(date):
    key = f'front-page-{date}'
    url = f'https://news.ycombinator.com/front?day={date}'
    return download_maybe(key, url)

def download_hn_search_page(query):
    key = f'query-{query}'
    url = f'https://hn.algolia.com/?dateRange=all&page=0&prefix=true&query={query}&sort=byPopularity&type=story'
    return download_maybe(key, url)

def find_points(s):
    match = re.search(r'(\d+) points', s)
    return int(match.group(1))

def find_articles_in_hn_query(fname, maxnum=float('infinity')):
    raw = py.path.local(fname).read()
    soup = BeautifulSoup(raw, features='lxml')
    for i, article in enumerate(soup.find_all('article', class_='Story')):
        if i >= maxnum:
            break
        #print(article.prettify())
        title = article.find('div', class_='Story_title').text
        meta = article.find('div', class_='Story_meta')
        href = meta.find('a').attrs['href']
        points = find_points(str(meta))
        yield HNArticle(points=points, title=title, href=href)

def find_date_in_article(article):
    match = re.search(r'item\?id=(\d+)', article.href)
    id = int(match.group(1))
    key = f'item-{id}'
    raw = download_maybe(key, article.href)
    soup = BeautifulSoup(raw, features='lxml')
    span = soup.find('span', class_='age')
    dt = span.attrs['title']
    date, time = dt.split('T')
    return date


def find_pypy_link_in_hn_front_page(date):
    raw = download_hn_front_page(date)
    soup = BeautifulSoup(raw, features='lxml')
    for i, tr in enumerate(soup.find_all('tr', class_="athing")):
        if 'pypy' in str(tr).lower():
            span_rank = tr.find('span', class_='rank')
            if span_rank is None:
                rank = '???'
            else:
                rank = int(span_rank.text.replace('.', ''))
            #
            titleline = tr.find('span', class_='titleline')
            #print(tr.prettify())
            assert titleline is not None
            title = titleline.text
            href = titleline.find('a').attrs['href']

            next_tr = tr.find_next_sibling()
            points = find_points(str(next_tr))
            yield PyPyLink(rank=rank, points=points, date=date, title=title, link=href)



def main():
    # you need to manually download this page because it requires JS
    # open in chrome dev tools, right click on "<html>", click "copy outer HTML", paste to file
    #url = 'https://hn.algolia.com/?dateRange=all&page=0&prefix=true&query=pypy&sort=byPopularity&type=story'

    articles = list(find_articles_in_hn_query('/tmp/hn-morepypy.html', maxnum=30))
    articles += list(find_articles_in_hn_query('/tmp/hn-pypyorg.html', maxnum=10))

    all_dates = []
    for art in articles:
        all_dates.append(find_date_in_article(art))
    all_dates.sort()

    pypy_links = []
    for date in all_dates:
        for link in find_pypy_link_in_hn_front_page(date):
            pypy_links.append(link)

    pypy_links.sort(key=lambda link: link.rank)

    # print articles, sorted by points
    ## for art in articles:
    ##     print(f'{art.points:4d} points    {art.title:50}') # {art.href}')
    ## print()
    ## print()

    # print links, sorted by rank in the front page of the day in which they were posted
    for link in pypy_links:
        print(f'{link.rank:2d}  {link.points} points   {link.date}    {link.title}    {link.link}')


if __name__ == '__main__':
    main()
