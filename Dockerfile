FROM ocaml/opam:debian

ENV DEBIAN_FRONTEND=noninteractive

RUN sudo apt-get update && sudo apt-get install -y \
    linux-libc-dev \
    pkg-config \
    libgmp-dev \
    graphviz \
    && sudo rm -rf /var/lib/apt/lists/*

WORKDIR /workspace

RUN opam repo add rocq-released https://rocq-prover.org/opam/released && \
    opam pin add rocq-core 9.2.0 && \
    opam install rocq-navi rocq-prover

COPY . /workspace
RUN sudo chown -R opam:opam /workspace
