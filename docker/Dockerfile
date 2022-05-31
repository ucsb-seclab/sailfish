FROM ubuntu:bionic
LABEL maintainer sherlock

ARG DEBIAN_FRONTEND=noninteractive
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en  
ENV LC_ALL en_US.UTF-8
ENV PYTHONIOENCODING UTF-8
ENV TZ=America/Los_Angeles
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt-get update && \
    apt-get install --yes apt-utils software-properties-common python3-pip python3-virtualenv locales \
                        git wget libfontconfig libcairo2 libpango-1.0.0 libpangocairo-1.0-0 libjpeg62-dev graphviz && \
    apt-get --yes autoremove && \
    apt-get --yes autoclean && \
    apt-get clean && \
    rm -rf /var/lib/apt/*
RUN locale-gen en_US.UTF-8
RUN python3 -m pip install --upgrade --force-reinstall pip
RUN ln -s /usr/bin/python3 /usr/bin/python
RUN sed -i "s/ls -alF/ls -lF/g" /root/.bashrc

WORKDIR /root

# Invalidate the cache to make sure we get the latest version of the code
ARG TIMESTAMP
RUN echo $TIMESTAMP > /dev/null

# Clone the repositories
RUN git clone --recursive https://github.com/ucsb-seclab/sailfish.git sailfish
RUN git clone https://github.com/ucsb-seclab/slither-sailfish.git slither
RUN git clone https://github.com/dipanjan/solc-binaries.git

# Configure Explorer
RUN pip3 install -r /root/sailfish/code/static_analysis/requirements.txt

# Configure Slither
RUN cd /root/slither && python3 setup.py install

# Configure Refiner
RUN wget --quiet https://mirror.racket-lang.org/installers/7.7/racket-7.7-x86_64-linux.sh && \
    chmod +x racket-7.7-x86_64-linux.sh && \
    ./racket-7.7-x86_64-linux.sh --in-place --dest /usr/racket --create-links /usr && \
    rm -f racket-7.7-x86_64-linux.sh
RUN raco pkg install --deps search-auto --type github --checksum e4b56fa --name rosette emina/rosette
RUN wget --quiet -O /usr/bin/cvc4 https://github.com/CVC4/CVC4/releases/download/1.7/cvc4-1.7-x86_64-linux-opt && \
    chmod +x /usr/bin/cvc4
RUN cd /root/sailfish/code/symbolic_execution && \
    git clean -fd && \
    ./build.py

# Install different versions of solc compiler
RUN ln -s /root/solc-binaries/.solc-select /root/.solc-select
RUN echo 'PATH=~/.solc-select:$PATH' >> /root/.bashrc && \
    chmod -R 755 /root/.solc-select

WORKDIR /root/sailfish/code/static_analysis/analysis
