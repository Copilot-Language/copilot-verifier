FROM ubuntu:focal

ENV LLVM_VER=12
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get install --yes clang-$LLVM_VER curl gcc g++ git libgmp3-dev libtinfo-dev libz-dev llvm-$LLVM_VER-tools make wget z3

ENV GHCUP_VER=0.1.22.0
RUN mkdir -p /root/.ghcup/bin
RUN wget https://downloads.haskell.org/~ghcup/$GHCUP_VER/x86_64-linux-ghcup-$GHCUP_VER -O /root/.ghcup/bin/ghcup && \
    chmod a+x /root/.ghcup/bin/ghcup

ENV PATH=/root/bsc/bin:/root/.cabal/bin:/root/.ghcup/bin:$PATH

ENV GHC_VER=9.2.8
ENV CABAL_VER=3.8.1.0
RUN ghcup install ghc $GHC_VER && \
    ghcup set ghc $GHC_VER && \
    ghcup install cabal $CABAL_VER && \
    ghcup set cabal $CABAL_VER && \
    cabal update

COPY . /copilot-verifier
WORKDIR /copilot-verifier

ENV LLVM_LINK="llvm-link-$LLVM_VER"
ENV LLVM_AS="llvm-as-$LLVM_VER"
ENV CLANG="clang-$LLVM_VER"
RUN cabal configure --enable-tests && \
    cabal build lib:copilot-verifier --write-ghc-environment-files=always && \
    cabal test copilot-verifier

ENTRYPOINT ["/usr/bin/bash"]
