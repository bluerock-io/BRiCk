#!/bin/sh -x
get_srcs_dunes() {
  find . -type f \( -name '*.v' -o -name '*.v.*' -o -name '*.rst' -o -name '*.elpi*' -o -name 'dune*' -o -name '*.opam' -o -name '*.ml' -o -name '*.t' -o -name '*.awk' -o -name '_CoqProject*' -o -name '*.md' -o -name '*.[ch]pp' -o -name 'setup-project.sh' \) -print0
}

SED=gsed
which -s $SED || SED=sed

get_srcs_dunes|xargs -0 $SED -i -E 's/\<bedrock(|_tests|_auto_core|_auto)\>/bluerock\1/g;s/\<db_bedrock(|_wp|_syntactic)\>/db_bluerock\1/g;'
