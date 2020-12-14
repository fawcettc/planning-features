## Installing

Installation of planning-features is currently the least-developed portion
of the project. This is mostly due to the third-party extractor dependencies
and their individual build scripts.

Most users should be able to get away with using our included build script:

    (planning-features/)$ ./build.sh

This will hopefully build each of the dependencies successfully. If any fail,
you will need to manually investigate the build process of that dependency.
Please contact us if you run into such issues and have difficulty resolving them.

### Docker

We have included a Dockerfile for building an Ubuntu 20.04 image containing the
planning-features extractors. If you have Docker installed, simply run the following from
the repository root:

    (planning-features/)$ docker build -t planning-features .

This will take some time, but you should end up with a *planning-features:latest* image.

You can test the image by extracting the features from our single example pddl:

    $ docker run -it --rm planning-features:latest /opt/planning-features/extract_planning_features.py --domain-file /opt/planning-features/examples/barman.pddl --instance-file /opt/planning-features/examples/ipc-agile-2014-barman-p1-11-4-15.pddl

You can utilize volumes in order to provide your own features for extraction, and
for storing the results:

    $ docker run -it --rm -v <some host directory>:/opt/planning-instances -v <some other host directory>:/opt/extracted-features planning-features:latest /opt/planning-features/extract_planning_features.py --domain-file /opt/planning-instances/<path to domain> --instance-file /opt/planning-instances/<path to instance> --json-output-file /opt/extracted-features/<path to output json> --csv-output-file /opt/extracted-features/<path to output CSV>

### Requirements

 * We currently require GNU/Linux (and likely only a subset of distributions) due
   to only having statically-linked binaries for some of the SATzilla extraction code.
   The project has been tested on modern CentOS, RHEL and Ubuntu servers with no issues,
   but we fully expect that there will be exceptions to this! Please let us know when you
   find any.

 * We require Python 2.7 for most of the extraction code. Most of our testing
   has been with 2.7.7 and 2.7.10.

 * The extractor dependencies, in most cases, have their own dependencies. Please
   see their documentation for full details.

### Testing your installation

The planning-features/examples directory contains a sample problem instance and domain,
along with the JSON and CSV feature output we obtained on a known-good system.
Simply run the feature extractor from an experiment directory as follows, and compare the output
with the reference:

    $ python <path to extractor>/planning-features/extract_planning_features.py --domain-file <path to extractor>/planning-features/examples/barman.pddl --instance-file <path to extractor>/planning-features/examples/ipc-agile-2014-barman-p1-11-4-15.pddl --json-output-file ./features.json --csv-output-file ./features.csv

 * Many feature values will vary slightly depending on the executing machine architecture,
   machine load, and the stochastic nature of the solvers used for probing features.
 * We recommend first comparing the values of the various *meta-success-** features, as they
   track the success or failure of entire extraction components.
 * Feature values of -512.0 for features that do not have these values in the reference results are also
   a concern, as this is a sentinel value signalling a failed extraction for that feature.
