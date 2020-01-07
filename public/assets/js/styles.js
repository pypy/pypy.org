'use strict';

// Navbar
/* Toggle between adding and removing the "responsive" class to topnav when the user clicks on the icon */
function make_responsive() {
  var x = document.getElementById("myTopNav");
  if (x.className === "topnav") {
    x.className += " responsive";
  } else {
    x.className = "topnav";
  }
} 
