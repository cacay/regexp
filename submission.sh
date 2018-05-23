#!/usr/bin/env bash

set -e

# Create a new temporary branch
git checkout -b dist

# Generate report.pdf
(cd paper && make && rm -f ../report.pdf && cp report.pdf ../)

# Commit report.pdf
git add -f report.pdf
git commit -m "Add paper"

# Create an archive containing the source code and the report
git archive --prefix=regexp/ -o dist.tar.gz HEAD

# Delete the temporary branch
git checkout master && git branch -D dist
