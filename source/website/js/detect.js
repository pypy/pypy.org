
$(document).ready(function() {
    var download_url, download_text;
    if (navigator.platform.indexOf('Linux') != -1) {
        download_url = 'download/pypy-1.2-linux.tar.bz2';
        download_text = 'Download linux x86 bin';
    } else if (navigator.platform.indexOf('Windows') != -1) {
        download_url = 'download/pypy-1.2-win32.zip';
        download_text = 'Download Windows bin';
    } else if (navigator.platform.indexOf('Mac') != 1) {
        download_url = 'download/pypy-1.2-osx.tar.bz2';
        downloat_text = 'Download Mac OS X 10.6 bin';
    } else {
        return;
    }
    $("#main_download").attr('href', download_url);
    $("#main_download").text(download_text);
});
