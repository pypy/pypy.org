'use strict';

// Navbar
(function () {
    // Swap simple navbar for smart navbar
    function swapNavbars() {
        var navbars = document.getElementsByClassName("js-navbar");
        [].forEach.call(navbars, function (navbar) {
            if (navbar.classList.contains("navbar")) {
                navbar.classList.remove("navbar");
                navbar.classList.add("navbar-smart");
                // also turn on the menu button
                var menuButtons = navbar.parentNode.getElementsByClassName("js-navbar-toggler");
                [].forEach.call(menuButtons, function (menuButton) {
                    menuButton.classList.add("navbar-menu-on");
                });
            }
        });
    }

    // Add event to show or hide the navbar menu when icon is clicked
    function toggleNavbarMenu() {
        var navbars = document.getElementsByClassName("js-navbar");

        [].forEach.call(navbars, function (navbar) {
            // only works with "navbar-smart"
            if (navbar.classList.contains("navbar-smart")) {
                var menuButtons = navbar.parentNode.getElementsByClassName("js-navbar-toggler");
                [].forEach.call(menuButtons, function (menuButton) {
                    menuButton.addEventListener('click', function (e) {
                        e.preventDefault();
                        var related_navbar = navbar;
                        related_navbar.classList.toggle('navbar-open');
                    });
                });
            }
        });
    }
    document.addEventListener("DOMContentLoaded", function () {
        swapNavbars();
        toggleNavbarMenu();
    });
})();
