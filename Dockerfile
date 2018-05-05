FROM ubuntu:16.04

RUN  apt-get update
RUN  apt-get install -y wget
RUN  apt-get install -y tar

FROM haskell:8.0.1

RUN stack --resolver nightly-2016-12-29 setup




