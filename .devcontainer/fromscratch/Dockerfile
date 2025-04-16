FROM ocaml/opam:ubuntu-24.04-ocaml-4.14

ENV OPAMJOBS=16
RUN sudo apt update
RUN sudo apt install -y wget unzip pkg-config libgmp-dev libssl-dev \
    python3 python3-pip python3-distutils-extra

RUN opam install z3.4.8.5 -y

ENV PATH="/home/opam/.opam/default/bin:$PATH"
ENV Z3_EXE="/home/opam/.opam/default/bin/z3"

RUN git clone https://github.com/FStarLang/FStar --depth 1 --branch master && \
    cd FStar && \
    opam install . -y --deps-only
RUN cd FStar && \
    opam install . -y

RUN git clone https://github.com/kayceesrk/karamel && \
    cd karamel && \
    opam install . -y --deps-only
RUN cd karamel && \
    opam install . -y

RUN git clone https://github.com/FStarLang/pulse && \
    cd pulse && \
    opam install . -y --deps-only
RUN cd pulse && \
    opam install . -y
