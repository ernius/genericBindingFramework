FROM haskell:8.0.1

RUN stack --resolver nightly-2016-12-29 setup
RUN stack install Agda
CMD agda




