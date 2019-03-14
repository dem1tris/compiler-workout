make check
export RC_RUNTIME=$(readlink -f "../runtime");
pushd expressions && make check && popd
pushd deep-expressions && make check && popd

