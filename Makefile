ifeq ($(origin .RECIPEPREFIX), undefined)
    $(error This Make does not support .RECIPEPREFIX. Please use GNU Make 4.0 or later)
endif
.RECIPEPREFIX = >

.PHONY: clean build help

venv_nikola/bin/nikola:  ## create a virtualenv to build the website
> virtualenv -ppython3 ./venv_nikola
> venv_nikola/bin/python -mpip install nikola==8.0.3 jinja2

build: venv_nikola/bin/nikola  ## build the website if needed, the result is in ./public
> venv_nikola/bin/nikola build

clean:  venv_nikola/bin/nikola  ## clean the website, usually not needed at all
> venv_nikola/bin/nikola clean

# Add help text after each target name starting with '\#\#'
help:   ## Show this help.
> @echo "\nHelp for building the website, based on nikola"
> @echo "Possible commands are:"
> @grep -h "##" $(MAKEFILE_LIST) | grep -v grep | sed -e 's/\(.*\):.*##\(.*\)/    \1: \2/'
 
