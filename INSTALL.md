## Compiling the development with Docker

We recommend compiling the development using Docker. To do this,

1. Make sure you have [Docker](https://docs.docker.com/get-docker/) installed.
2. Run `docker build -t="axsl:popl" .` to build the Docker image.

The building process may take up to one hour, including installing dependencies and compilation. 

Optionally, you can follow this by executing `docker run -i -t axsl:popl` to start a container with the freshly built image and access
an interactive shell inside it.

### Troubleshooting

In order to build the development, you might have to increase the amount of
memory allocated to a running Docker container. For
instructions, see
[here](https://stackoverflow.com/questions/44533319/how-to-assign-more-memory-to-docker-container).


## Manually Installing with opam

### Opam and ocaml

All dependencies install instruction assume you can use `opam`. If needed,
instructions are available here: https://opam.ocaml.org/doc/Install.html.

You need to add the coq opam repository for some of the dependencies:
```
opam repo add coq-released https://coq.inria.fr/opam/released
```


### Dune

This project uses the dune build system. It can be installed with:
```
opam install dune
```


### Coq

Install Coq `8.18.0`
```
opam pin coq 8.18.0
```

### Coq libraries

#### Iris and stdpp

You need to add the iris opam repository to install Iris and stdpp :
```
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

This development uses Iris 4.2.0:
```
opam install coq-iris.4.2.0 -y
```

This development uses `stdpp` and `stdpp-bitvector` 1.10.0: 
```
opam install coq-stdpp.1.10.0 -y
opam install coq-stdpp-bitvector.1.10.0 -y
```

#### iris-named-props

This development uses a small Iris extension `iris-named-prop`.

Clone it with
```
git clone https://github.com/tchajed/iris-named-props.git
```

In the cloned directory, check out to the version that has been tested:
```
git checkout 327119f
```

Install with opam:
```
opam pin . -y
```


#### Coq Record Update

This repository use the Coq record update library. To install it do:
```
opam install coq-record-update
```

#### Dependencies of system-semantics

Install the libraries listed in `system-semantics/INSTALL.md` but not mentioned above

### Build the development

In the directory, run:

```
dune build
```
