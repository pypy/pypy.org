
function py3k_donate() {
    $.get("don1.html", function (html) {
        $("#sidebar").html(html);
    });
}

function general_donate() {
    $.get("don2.html", function (html) {
        $("#sidebar").html(html);
    });
}

function numpy_donate() {
    $.get("don3.html", function (html) {
        $("#sidebar").html(html);
    });
}

$(document).ready(function() {
    numpy_donate();
});