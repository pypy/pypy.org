
function py3k_donate() {
    $.get("donate1.html", function (html) {
        $("#sidebar").html(html);
    });
}

function general_donate() {
    $.get("donate2.html", function (html) {
        $("#sidebar").html(html);
    });
}

function numpy_donate() {
    $.get("donate3.html", function (html) {
        $("#sidebar").html(html);
    });
}

$(document).ready(function() {
    numpy_donate();
});