FROM ubuntu:16.04

# RUN  apt-get update
# RUN  apt-get install -y wget
# RUN  apt-get install -y tar

RUN wget https://github.com/agda/agda-stdlib/archive/v0.13.tar.gz -O /tmp/v0.13.tar.gz
RUN tar -xzvf /tmp/v0.13.tar.gz -C /tmp/

FROM haskell:8.0.1

RUN stack --resolver nightly-2016-12-29 setup
RUN stack install Agda
RUN agda -i . -i /tmp/agda-stdlib-0.13/src/ Examples/SystemF.lagda Examples/LambdaCalculus.lagda
