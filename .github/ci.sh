#!/usr/bin/env bash
set -Eeuxo pipefail

DATE=$(date "+%Y-%m-%d")
[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

install_llvm() {
  if [[ "$RUNNER_OS" = "Linux" ]]; then
    sudo apt-get update -q && sudo apt-get install -y clang-$LLVM_VERSION llvm-$LLVM_VERSION-tools
  else
    echo "$RUNNER_OS is not currently supported."
    return 1
  fi
  echo "CLANG=clang-$LLVM_VERSION" >> "$GITHUB_ENV"
  echo "LLVM_AS=llvm-as-$LLVM_VERSION" >> "$GITHUB_ENV"
  echo "LLVM_LINK=llvm-link-$LLVM_VERSION" >> "$GITHUB_ENV"
}

install_solvers() {
  (cd $BIN && curl -o bins.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/$SOLVER_PKG_VERSION/$BUILD_TARGET_OS-bin.zip" && unzip -o bins.zip && rm bins.zip)
  cp $BIN/yices_smt2$EXT $BIN/yices-smt2$EXT
  chmod +x $BIN/*
}

install_system_deps() {
  install_solvers
  install_llvm
  # wait
  export PATH=$PWD/$BIN:$PATH
  echo "$PWD/$BIN" >> $GITHUB_PATH
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" cvc5 && is_exe "$BIN" yices
}

COMMAND="$1"
shift

"$COMMAND" "$@"
