#! /usr/bin/env python
#
# Prune an existing feature file (in CSV or JSON format) given a list of
# instances to retain or remove.

from __future__ import print_function

import argparse
import sys
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

def read_pruning_file(filepath):
    # return list of instance keys for pruning. Always the first column of the input CSV.
    pruning_keys = []

    with open(filepath, 'r') as f:
        first = True
        for line in f:
            components = line.lstrip().rstrip().split(',')

            if first:
                # ignore the header line
                first = False
            else:
                instance_key = components[0].lstrip('"').rstrip('"').lstrip("'").rstrip("'")

                pruning_keys.append(instance_key)

    return pruning_keys

def main():
    parser = argparse.ArgumentParser(description="", formatter_class=argparse.RawDescriptionHelpFormatter, add_help=True)

    parser.add_argument("--features-file", dest="features_file", default=None, type=str, help="Path to features file in CSV or JSON format")
    parser.add_argument("--features-to-remove", dest="features_to_remove", default=None, type=str, help="Path to CSV file (with header) where the first column contains instance paths matching the feature keys. Features for instances with these keys will be removed in the output.")
    parser.add_argument("--features-to-retain", dest="features_to_retain", default=None, type=str, help="Path to CSV file (with header) where the first column contains instance paths matching the feature keys. Features for instances with these keys will be retained in the output. If a key is in both the removal and retention files, that instance will be removed.")
    parser.add_argument("--format", dest="format", default="CSV", type=str, choices=["CSV", "JSON"], help="format for the feature-file argument")
    parser.add_argument("--output-file", dest="output_file", default=None, type=str, help="Path to a file that will contain all features retained after pruning, in the same format as the input.")

    args = parser.parse_args()

    features = {}

    if args.format == 'CSV':
        features.update(read_feature_file_csv(args.features_file))
    elif args.format == 'JSON':
        features.update(read_feature_file_json(args.features_file))

    if args.features_to_remove != None:
        # read removal file, remove those instances
        removal_keys = read_pruning_file(args.features_to_remove)
        features = {key:value for (key,value) in features.iteritems() if key not in removal_keys}

    if args.features_to_retain != None:
        # read retention file, remove all *other* instances
        retention_keys = read_pruning_file(args.features_to_retain)
        features = {key:value for (key,value) in features.iteritems() if key in retention_keys}

    if args.format == 'CSV':
        write_feature_file_csv(features, args.output_file)
    elif args.format == 'JSON':
        write_feature_file_json(features, args.output_file)

    print("Output pruned features for {} instances in {} format.".format(len(features), args.format))

if __name__ == "__main__":
    main()
