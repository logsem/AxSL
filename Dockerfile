ARG BASE_TAG="latest"
FROM coqorg/coq:8.16.1-ocaml-4.14.1-flambda

COPY --chown=coq . /artifact/axsl
WORKDIR /artifact

# hadolint ignore=SC2046
RUN sudo apt-get update && sudo apt-get install zlib1g-dev -y

RUN eval $(opam env --set-switch) \
    && opam update -y -u \
    && opam config list && opam repo list && opam list \
    && opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

RUN git clone https://github.com/rems-project/coq-sail \
    && cd coq-sail \
    && git checkout aeca2c5 \
    && opam pin . -y

RUN opam install axsl/. --deps-only -y

RUN git clone https://github.com/tchajed/iris-named-props.git \
    && cd iris-named-props \
    && git checkout 327119f \
    && opam pin . -y

RUN opam list \
    && cd axsl \
    && dune build --display short
