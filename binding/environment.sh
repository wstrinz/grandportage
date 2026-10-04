# Source before lake commands: keeps toolchain caches and scratch on F:.
export BINDING_ROOT=binding
export PATH=$ELAN_HOME/toolchains/leanprover--lean4---v4.34.0-rc2/bin:$PATH
export TEMP=$BINDING_ROOT/tmp TMP=$BINDING_ROOT/tmp
export XDG_CACHE_HOME=$BINDING_ROOT/cache
export MATHLIB_CACHE_DIR=$BINDING_ROOT/cache/mathlib
export MATHLIB_NO_CACHE_ON_UPDATE=1
export GIT_TERMINAL_PROMPT=0
