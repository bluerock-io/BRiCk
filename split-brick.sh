sed -i -E 's/bedrock.lang.((bi)|(algebra)|(tactic)|(base_logic)|(si_logic)|(proofmode))/bedrock.iris.extra.\1/g' `find . -iname '*.v' -type f`
sed -i -E 's/bedrock.lang.cpp.$/bedrock.lang.cpp.cpp./g' `find . -iname '*.v' -type f`
sed -i -E 's/bedrock.iris.extra.base_logic.mpred_prop/bedrock.lang.cpp.logic.mpred_prop/g' `find . -iname '*.v' -type f`
sed -i -E 's/bedrock.iris.extra.base_logic.lib.spectra_mpred/bedrock.lang.cpp.logic.spectra_mpred/g' `find . -iname '*.v' -type f`
sed -i -E 's/bedrock.lang/bedrock.iris.extra bedrock.lang.cpp/g' `find . -iname dune`
