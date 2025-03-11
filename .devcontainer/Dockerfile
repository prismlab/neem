# Use an Ubuntu base image (you can use another base if needed)
FROM ubuntu:20.04

# Set the working directory inside the container
WORKDIR /workspace

# Install necessary dependencies
RUN apt-get update \
    && apt-get install -y \
    curl \
    git \
    opam \
    build-essential \
    m4 \
    zlib1g-dev \
    libgmp-dev \
    libffi-dev \
    libssl-dev \
    unzip \
    wget \
    gcc \
    g++ \
    make \
    libncurses5-dev \
    libncursesw5-dev \
    pkg-config \
    ocaml \
    python3 \
    python3-pip \
    && apt-get clean

# Install F* dependencies via OPAM (OCaml package manager)
RUN opam init -y \
    && opam update \
    && opam switch create 4.12.0 \
    && eval $(opam env) \
    && opam install fstar

# Clone the F* repository (if you need the source code)
RUN git clone https://github.com/FStarLang/FStar.git /workspace/FStar

# Set up OPAM environment for F* project
RUN echo 'eval $(opam env)' >> ~/.bashrc

# Expose a default port if needed (for any internal server, etc.)
EXPOSE 8080

# Set the default command for the container
CMD ["bash"]

