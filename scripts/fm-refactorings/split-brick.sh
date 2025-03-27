#!/bin/sh -v
get_srcs() {
  find . -type f \( -iname '*.v' -o -iname '*.rst' \)
}
get_dunes() {
  find . -iname dune
}

SED=gsed
which -s $SED || SED=sed

$SED -i -E 's/bedrock.lang.((bi)|(algebra)|(tactic)|(base_logic)|(si_logic)|(proofmode))/bedrock.iris.extra.\1/g' $(get_srcs)
$SED -i -E 's/bedrock.lang.cpp.$/bedrock.lang.cpp.cpp./g' $(get_srcs)
$SED -i -E 's/bedrock.iris.extra.base_logic.mpred_prop/bedrock.lang.cpp.logic.mpred_prop/g' $(get_srcs)
$SED -i -E 's/bedrock.iris.extra.base_logic.lib.spectra_mpred/bedrock.lang.cpp.logic.spectra_mpred/g' $(get_srcs)
$SED -i -E 's/bedrock.lang/bedrock.iris.extra bedrock.lang.cpp/g' $(get_dunes)
