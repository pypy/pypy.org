from py.__.documentation.confrest import *

class PyPyPage(Page): 
    def fill(self):
        super(PyPyPage, self).fill()
        self.menubar[:] = html.div(
            html.a("home", href="home.html", class_="menu"), " ",
            html.a("news", href="news.html", class_="menu"), " ",
            html.a("consortium", href="consortium.html", class_="menu"), " ",
            " ", id="menubar")

class Project(Project): 
    title = "PyPy EU Project" 
    stylesheet = 'style.css'
    encoding = 'latin1' 
    prefix_title = "EU/PyPy"
    logo = html.div(
        html.a(
            html.img(alt="PyPy", id="pyimg", 
                     src="http://codespeak.net/pypy/img/py-web1.png", 
                     height=110, width=149)))
    Page = PyPyPage 


