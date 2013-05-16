function set_sidebar_html(html) {
    $("#sidebar").html(html);
}

function py3k_donate() {
    $.get("don1.html", set_sidebar_html);
}

function stm_donate() {
    $.get("don4.html", set_sidebar_html);
}

function general_donate() {
    $.get("don2.html", set_sidebar_html);
}

function numpy_donate() {
    $.get("don3.html", set_sidebar_html);
}

$(document).ready(stm_donate);
