FROM haskell:8.0.2

RUN cabal update
RUN cabal install Agda-2.5.2
RUN wget https://github.com/agda/agda-stdlib/archive/v0.13.tar.gz -O /tmp/v0.13.tar.gz
RUN tar -xzvf /tmp/v0.13.tar.gz -C /tmp/
RUN agda -i . -i /tmp/agda-stdlib-0.13/src/ Examples/SystemF.lagda Examples/LambdaCalculus.lagda
