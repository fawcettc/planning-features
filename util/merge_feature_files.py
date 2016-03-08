#!/usr/bin/env python2.7
# encoding: utf-8
'''
    merge_feature_files -- make merged feature files in CSV and JSON format


    merge_feature_files is a script to create a single feature file containing features
    for several instances, using source feature files from a given directory

    Copyright (C) 2016 Chris Fawcett (fawcettc@cs.ubc.ca)
'''

from __future__ import print_function

import sys
import os
import re
from argparse import ArgumentParser, RawDescriptionHelpFormatter
import shutil
import json

def read_feature_file_csv(filepath):
    features = {}

    with open(filepath, 'r') as f:
        header_values = []
        first = True
        for line in f:
            components = line.lstrip().rstrip().split(',')

            if first:
                header_instance_key = components[0].lstrip('"').rstrip('"')
                header_feature_keys = map(lambda x: x.lstrip('"').rstrip('"'), components[1:])

                first = False
            else:
                instance_key = components[0].lstrip('"').rstrip('"')
                feature_values = components[1:]

                instance_features = {}
                for feature_key,feature_value in zip(header_feature_keys, feature_values):
                    instance_features[feature_key] = feature_value

                features[instance_key] = instance_features

    return features

def read_feature_file_json(filepath):
    features = {}

    with open(filepath, 'r') as f:
        features_json = json.load(f)
        features = features_json['instance_features']

    return features

def write_feature_file_csv(features, filepath):
    # all instances have been verified to have the same features, so just use
    # a sorted list of keys from the first instance as the header
    instance_keys = sorted(features.keys())
    feature_keys = sorted(features[instance_keys[0]].keys())

    with open(filepath, 'w') as f:
        print("\"{}\",\"{}\"".format("instanceName", "\",\"".join(feature_keys)), file=f)
        for instance in instance_keys:
            feature_values = [features[instance][feature] for feature in feature_keys]
            print ("\"{}\",{}".format(instance, ",".join(feature_values)), file=f)

def write_feature_file_json(features, filepath):
    with open(filepath, 'w') as f:
        print("{", file=f)
        print("    \"instance_features\": {", file=f)

        count_instances = 0
        for instance,instance_features in features.iteritems():
            print("        \"{}\": {{".format(instance), file=f)

            count_features = 0
            for feature,value in instance_features.iteritems():
                if count_features < len(instance_features)-1:
                    feature_sep = ","
                else:
                    feature_sep = ""

                print("            \"{}\": {}{}".format(feature, str(value), feature_sep), file=f)

                count_features += 1

            if count_instances < len(features)-1:
                instance_sep = ","
            else:
                instance_sep = ""

            print("        }}{}".format(instance_sep), file=f)
            count_instances += 1

        print("    }", file=f)
        print("}", file=f)

def validate_features(features):
    feature_keys = sorted(features[features.keys()[0]].keys())

    for instance,features in features.iteritems():
        if len(features) != len(feature_keys):
            print("ERROR: instance {} has {} features when it should have {}.".format(instance, len(features), len(feature_keys)), file=sys.stderr)

        for test_feature in feature_keys:
            if test_feature not in features:
                print("ERROR: instance {} does not contain feature {}.".format(instance, test_feature), file=sys.stderr)


def main():
    parser = ArgumentParser(description="", formatter_class=RawDescriptionHelpFormatter, add_help=True)

    parser.add_argument("source_files", metavar='FILE', type=str, nargs='*', help="zero or more source feature files. Should not contain files in --source-directory")
    parser.add_argument("--source-directory", dest="source_directory", default=None, type=str, help="path a directory containing the feature files to merge")
    parser.add_argument("--format", dest="format", default="CSV", choices=["CSV","JSON"], type=str, help="file format of the source and output feature files")
    parser.add_argument("--output-path", dest="output_path", default=None, type=str, help="path to store the output merged feature file")

    args = parser.parse_args()

    features = {}

    for source_file in args.source_files:
        if args.format == 'CSV':
            features.update(read_feature_file_csv(source_file))
        elif args.format == 'JSON':
            features.update(read_feature_file_json(source_file))

    if args.source_directory != None:
        for feature_file in os.listdir(args.source_directory):
            if args.format == 'CSV':
                features.update(read_feature_file_csv("{}/{}".format(args.source_directory, feature_file)))
            elif args.format == 'JSON':
                features.update(read_feature_file_json("{}/{}".format(args.source_directory, feature_file)))

    validate_features(features)

    if args.format == 'CSV':
        write_feature_file_csv(features, args.output_path)
    elif args.format == 'JSON':
        write_feature_file_json(features, args.output_path)

    print("Output features for {} instances in {} format.".format(len(features), args.format))

if __name__ == "__main__":
    main()
