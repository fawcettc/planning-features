#!/usr/bin/env python2.7
# encoding: utf-8
'''
extract_features -- extract planning instance and domain features

extract_features is a script to extract scalar features from
a given PDDL planning instance and domain, using several component
extractors.

@author:     Chris Fawcett
@copyright:  TBD
@license:    TBD

@contact:    fawcettc@cs.ubc.ca
'''

import sys
import os
from argparse import ArgumentParser, RawDescriptionHelpFormatter
from subprocess import Popen, PIPE
import shutil

import extractors

__version__ = 0.1
__authors__ = 'Chris Fawcett'
__date__ = '2013-11-15'
__updated__ = '2015-11-22'

__default_mem_limit__ = 6144
__default_per_extraction_time_limit__ = 1800

class TopLevelFeatureExtractor(extractors.FeatureExtractor):
    def __init__(self, args):
        super(TopLevelFeatureExtractor, self).__init__(args)

        self.extractors = []

        if args.extract_simple_pddl:
            self.extractors.append(extractors.SimplePDDLFeatureExtractor(args))

        if args.extract_sas:
            self.extractors.append(extractors.SASFeatureExtractor(args))

    def extract(self, domain_path, instance_path):
        all_features = {}

        sas_representation_dir = None

        for extractor in self.extractors:
            try:
                if extractor.requires_sas_representation:
                    extractor.sas_representation_dir = sas_representation_dir

                features = extractor.extract(domain_path, instance_path)
                all_features.update(features)

                if extractor.creates_sas_representation:
                    sas_representation_dir = extractor.sas_representation_dir
            except:
                all_features.update(extractor.default_features())

        if sas_representation_dir != None:
            shutil.rmtree(sas_representation_dir)

        return all_features

if __name__ == "__main__":
    program_version = "v%s" % __version__
    program_update_date = str(__updated__)
    program_msg = "%%(prog)s %s (%s)" % (program_version, program_update_date)
    program_shortmsg = __import__("__main__").__doc__.split("\n")[1]
    program_license = '''%s
        Created by %s on %s.
        Copyright 2015 - TBD INSERT COPYRIGHT INFO. All rights reserved.

        Licensed under TBD INSERT LICENSE INFO

        LPG, Fast Downward, Torchlight and runsolver appear with permission from their
        respective authors, with their own licenses. Please see the respective
        source folders for that information.

        Distributed on an "AS IS" basis without warranties or conditions
        of any kind, either express or implied.

        USAGE
    ''' % (program_shortmsg, str(__authors__), str(__date__))

    abs_script_directory = os.path.abspath(os.path.dirname(sys.argv[0]))

    parser = ArgumentParser(description=program_license, formatter_class=RawDescriptionHelpFormatter, add_help=True)

    parser.add_argument("--runsolver-path", dest="runsolver", default=abs_script_directory+"/runsolver/runsolver", help="path to the runsolver binary (used for enforcing runtime and memory limits)")
    parser.add_argument("--mem-limit", dest="mem_limit", default=__default_mem_limit__, type=int, help="memory limit for extraction, in MiB")
    parser.add_argument("--per-extraction-time-limit", dest="per_extraction_time_limit", default=__default_per_extraction_time_limit__, type=float, help="CPU time limit for each component feature extraction, in seconds")

    parser.add_argument("--domain-file", dest="domain_file", default=None, type=str, help="PDDL domain file for feature extraction")
    parser.add_argument("--instance-file", dest="instance_file", default=None, type=str, help="PDDL instance file for feature extraction")

    parser.add_argument("--no-csv-header", dest="csv_header", action='store_false', help="Do not print the CSV header line")
    parser.set_defaults(csv_header=True)

    # simple pddl
    parser.add_argument("--extract-simple-pddl", dest="extract_simple_pddl", action='store_true', help="Extract simple PDDL features")
    parser.add_argument("--no-extract-simple-pddl", dest="extract_simple_pddl", action='store_false', help="Disable simple PDDL features")
    parser.set_defaults(extract_simple_pddl=True)

    parser.add_argument("--simple-pddl-no-extended-features", dest="simple_pddl_extended_features", action='store_false', help="Do not extract the extended PDDL features")
    parser.set_defaults(simple_pddl_extended_features=True)

    # SAS+ features
    parser.add_argument("--extract-sas", dest="extract_sas", action="store_true", help="Extract features from the SAS+ problem representation")
    parser.add_argument("--no-extract-sas", dest="extract_sas", action="store_false", help="Disable SAS+ features")
    parser.set_defaults(extract_sas=True)

    parser.add_argument("--sas-no-graph-features", dest="sas_graph_features", action="store_false", help="Do not extract the SAS+ graph features")
    parser.set_defaults(sas_graph_features=True)

    args = parser.parse_args(sys.argv[1:])

    # check to make sure the domain and instance exist
    if os.path.exists(args.domain_file):
        domain_file = os.path.abspath(args.domain_file)
    else:
        print "ERROR: Domain file %s does not exist!" % args.domain_file
        sys.exit(1)

    if os.path.exists(args.instance_file):
        instance_file = os.path.abspath(args.instance_file)
    else:
        print "ERROR: Instance file %s does not exist!" % args.instance_file
        sys.exit(1)

    top_level_extractor = TopLevelFeatureExtractor(args)
    features = top_level_extractor.extract(domain_file, instance_file)

    sorted_features = features.items()
    sorted_features.sort(key=lambda x: x[0])

    keys = [str(key) for key,value in sorted_features]
    values = [str(value) for key,value in sorted_features]

    if args.csv_header:
        print '"%s"' % '","'.join(keys)

    print '"%s"' % '","'.join(values)

    sys.exit(0)
