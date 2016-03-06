#!/usr/bin/env python2.7
# encoding: utf-8
'''
    extract_planning_features -- extract planning instance and domain features

    extract_planning_features is a script to extract scalar features from
    a given PDDL planning instance and domain, using several component
    extractors.

    Copyright (C) 2013-2016 Chris Fawcett (fawcettc@cs.ubc.ca)

    LPG, Fast Downward, Torchlight, Mp, SATzilla and runsolver appear with permission from their
    respective authors, with their own licenses. Please see the respective
    source folders for that information.


    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as
    published by the Free Software Foundation, either version 3 of the
    License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
'''

from __future__ import print_function

import sys
import os
from argparse import ArgumentParser, RawDescriptionHelpFormatter
from subprocess import Popen, PIPE
import shutil
import time

import extractors

__version__ = 0.1
__authors__ = 'Chris Fawcett'
__date__ = '2013-11-15'
__updated__ = '2016-01-12'

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

        if args.extract_lpg_probing:
            self.extractors.append(extractors.LPGProbingFeatureExtractor(args))

        if args.extract_sas and args.extract_fd_probing:
            self.extractors.append(extractors.FDProbingFeatureExtractor(args))
        elif args.extract_fd_probing:
            print("ERROR: You must have SAS+ features enabled if FD probing features are enabled.",file=sys.stderr)

        if args.extract_sat:
            self.extractors.append(extractors.SATFeatureExtractor(args))

        if args.extract_torchlight:
            self.extractors.append(extractors.TorchlightFeatureExtractor(args))

    def extract(self, domain_path, instance_path):
        all_features = {}

        sas_representation_dir = None

        for extractor in self.extractors:
            start_time = time.time()

            try:
                if extractor.requires_sas_representation:
                    extractor.sas_representation_dir = sas_representation_dir

                successful,features = extractor.extract(domain_path, instance_path)
                end_time = time.time()

                if extractor.creates_sas_representation:
                    sas_representation_dir = extractor.sas_representation_dir
            except:
                successful = False
                features = extractor.default_features()
                end_time = time.time()

            all_features.update(features)

            elapsed = end_time-start_time
            success_value = "0"
            if successful:
                success_value = "1"

            all_features.update({("meta-time-%s" % extractor.extractor_name):str(elapsed), ("meta-success-%s" % extractor.extractor_name):success_value})

        if sas_representation_dir != None:
            shutil.rmtree(sas_representation_dir)

        return {instance_path:all_features}

def export_features_csv(features, print_header=True, output_file=sys.stdout):
    # features is a dictionary {instance : {feature_name:feature_value}}

    sorted_feature_names = None
    for instance,instance_features in features.iteritems():
        if sorted_feature_names == None:
            sorted_feature_names = instance_features.keys()
            sorted_feature_names.sort()

            if print_header:
                print('"instanceName","%s"' % '","'.join(sorted_feature_names), file=output_file)

        values = [str(instance_features[name]) for name in sorted_feature_names]
        print('"%s",%s' % (instance, ','.join(values)), file=output_file)

def export_features_json(features, output_file=sys.stdout):
    # features is a dictionary {instance : {feature_name:feature_value}}

    print("{", file=output_file)
    print("    \"instance_features\": {", file=output_file)

    count_instances = 0
    for instance, instance_features in features.iteritems():
        print("        \"%s\": {" % instance, file=output_file)

        count_features = 0
        for feature,value in instance_features.iteritems():
            if count_features < len(instance_features)-1:
                feature_sep = ","
            else:
                feature_sep = ""

            print("            \"%s\": %s%s" % (feature, str(value), feature_sep), file=output_file)

            count_features += 1

        if count_instances < len(features)-1:
            instance_sep = ","
        else:
            instance_sep = ""

        print("        }%s" % instance_sep, file=output_file)
        count_instances += 1

    print("    }", file=output_file)
    print("}", file=output_file)

if __name__ == "__main__":
    program_version = "v%s" % __version__
    program_update_date = str(__updated__)
    program_msg = "%%(prog)s %s (%s)" % (program_version, program_update_date)
    program_shortmsg = __import__("__main__").__doc__.split("\n")[1]

    abs_script_directory = os.path.abspath(os.path.dirname(sys.argv[0]))

    parser = ArgumentParser(description=program_shortmsg, formatter_class=RawDescriptionHelpFormatter, add_help=True)

    parser.add_argument("--runsolver-path", dest="runsolver", default=abs_script_directory+"/runsolver/runsolver", help="path to the runsolver binary (used for enforcing runtime and memory limits)")
    parser.add_argument("--mem-limit", dest="mem_limit", default=__default_mem_limit__, type=int, help="memory limit for extraction, in MiB")
    parser.add_argument("--per-extraction-time-limit", dest="per_extraction_time_limit", default=__default_per_extraction_time_limit__, type=float, help="CPU time limit for each component feature extraction, in seconds")

    parser.add_argument("--domain-file", dest="domain_file", default=None, type=str, help="PDDL domain file for feature extraction")
    parser.add_argument("--instance-file", dest="instance_file", default=None, type=str, help="PDDL instance file for feature extraction")
    parser.add_argument("--bulk-extraction-file", dest="bulk_extraction_file", default=None, type=str, help="File containing many <domain,instance> pairs, in CSV format, domain in column 1 and instance in column 2, with each path double-quoted. A header row is assumed.")

    parser.add_argument("--csv-output-file", dest="csv_output_file", default="STDOUT", help="File in which to store the computed features in CSV format. Use STDOUT to print to stdout.")
    parser.add_argument("--no-csv-header", dest="csv_header", action='store_false', help="Do not print the CSV header line")
    parser.set_defaults(csv_header=True)

    parser.add_argument("--json-output-file", dest="json_output_file", default=None, help="File in which to store the computed features in JSON format. Use STDOUT to print to stdout.")

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

    # LPG probing
    parser.add_argument("--extract-lpg-probing", dest="extract_lpg_probing", action="store_true", help="Extract features using LPG probing runs")
    parser.add_argument("--no-extract-lpg-probing", dest="extract_lpg_probing", action="store_false", help="Disable LPG probing features")
    parser.set_defaults(extract_lpg_probing=True)

    # FD probing
    parser.add_argument("--extract-fd-probing", dest="extract_fd_probing", action="store_true", help="Extract features using FD probing runs")
    parser.add_argument("--no-extract-fd-probing", dest="extract_fd_probing", action="store_false", help="Disable FD probing features")
    parser.set_defaults(extract_fd_probing=True)

    # SAT
    parser.add_argument("--extract-sat", dest="extract_sat", action="store_true", help="Extract features using translation to SAT")
    parser.add_argument("--no-extract-sat", dest="extract_sat", action="store_false", help="Disable SAT features")
    parser.set_defaults(extract_sat=True)

    # Torchlight
    parser.add_argument("--extract-torchlight", dest="extract_torchlight", action="store_true", help="Extract features using Torchlight")
    parser.add_argument("--no-extract-torchlight", dest="extract_torchlight", action="store_false", help="Disable Torchlight features")
    parser.set_defaults(extract_torchlight=True)

    args = parser.parse_args(sys.argv[1:])

    top_level_extractor = TopLevelFeatureExtractor(args)

    # check to make sure the domain and instance exist
    if args.bulk_extraction_file:
        bulk_extraction_file = os.path.abspath(args.bulk_extraction_file)

        features = {}
        with open(bulk_extraction_file, 'r') as f:
            first = True
            for line in f:
                if not first:
                    line = line.lstrip().rstrip()
                    components = line.split(",")
                    components = map(lambda x: x.lstrip('"').rstrip('"'), components)

                    domain_file = os.path.abspath(components[0])
                    instance_file = os.path.abspath(components[1])

                    instance_features = top_level_extractor.extract(domain_file, instance_file)
                    features.update(instance_features)
                else:
                    first = False

    elif os.path.exists(args.domain_file) and os.path.exists(args.instance_file):
        domain_file = os.path.abspath(args.domain_file)
        instance_file = os.path.abspath(args.instance_file)

        features = top_level_extractor.extract(domain_file, instance_file)

    else:
        print("ERROR: You must specify either --bulk-extraction-file or both --domain-file and --instance-file.", file=sys.stderr)
        sys.exit(1)

    if features and args.csv_output_file:
        if args.csv_output_file == "STDOUT":
            export_features_csv(features, print_header=args.csv_header, output_file=sys.stdout)
        else:
            with open(os.path.abspath(args.csv_output_file), 'w') as f:
                export_features_csv(features, print_header=args.csv_header, output_file=f)

    if features and args.json_output_file:
        if args.json_output_file == "STDOUT":
            export_features_json(features, output_file=sys.stdout)
        else:
            with open(os.path.abspath(args.json_output_file), 'w') as f:
                export_features_json(features, output_file=f)

    sys.exit(0)
