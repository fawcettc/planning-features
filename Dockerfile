FROM ubuntu:20.04

RUN apt-get update && apt-get install -y build-essential bison flex python python2.7

# there are 32-bit binaries for SATzilla, we need to make sure they are runnable
RUN apt-get install -y gcc-multilib g++-multilib

# ensure we're using python2.7 and not python 3
RUN update-alternatives --install /usr/bin/python python /usr/bin/python2.7 10
RUN update-alternatives --set python /usr/bin/python2.7

# build all of the non-python portions of planning-features
ADD ./ /opt/planning-features
RUN cd /opt/planning-features && ./build.sh

CMD ["/bin/bash"]
