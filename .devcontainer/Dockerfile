FROM ubuntu:20.04
ENV DEBIAN_FRONTEND=noninteractive
WORKDIR /opt
COPY ./fstar /opt/FStar
WORKDIR /opt/FStar
ENV PATH="/opt/FStar/bin:$PATH"
COPY ./z3-4.8.5 /opt/z3
ENV Z3_HOME="/opt/z3"
ENV PATH="$Z3_HOME:$PATH"
RUN mkdir -p /code/
COPY code/ /code/
COPY verify_mrdts.sh /verify_mrdts.sh
COPY verify_crdts.sh /verify_crdts.sh
COPY README.md /README.md
COPY log/ /log/
WORKDIR /