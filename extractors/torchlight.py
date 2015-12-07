#!/usr/bin/env python2.7
# encoding: utf-8

from feature_extractor import FeatureExtractor

import os
import sys
import re
import shutil

class TorchlightFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(TorchlightFeatureExtractor, self).__init__(args)

    def default_features(self):
        base_features = [
            'torchlight-successPercentage',
            'torchlight-deadEndPercentage',
            'torchlight-exitDistanceMin',
            'torchlight-exitDistanceMean',
            'torchlight-exitDistanceMax',
            'torchlight-easyActionTemplates',
            'torchlight-hardActionTemplates',
            'torchlight-reachabilityFacts',
            'torchlight-reachabilityActions',
            'torchlight-relevantFacts',
        ]

        defaults = { key : self.sentinel_value for key in base_features }

        return defaults

    def extract(self, domain_path, instance_path):
        features = self.default_features()

        path_to_lpg = "%s/torchlight/torchlight" % (self.abs_script_directory)
        lpg_command = [path_to_lpg, "-o", domain_path, "-f", instance_path, "-Z"]

        try:
            output_directory = self.execute_command_with_runsolver(lpg_command, None, None)

            with open("%s/cmd.stdout" % (output_directory), 'r') as f:
                output = f.read()

                torchlight_features = self.extract_features(output)
                features.update(torchlight_features)

        except Exception as e:
            print "Exception running Torchlight: %s" % (str(e))
        finally:
            shutil.rmtree(output_directory)

        return features

    def extract_features(self, output):
        torchlight_features = {}

        success_percentage_match = re.search("Success and hence no local minima under h\+:\s+([0-9\.]*)%", output)
        if success_percentage_match:
            torchlight_features['torchlight-successPercentage'] = float(success_percentage_match.group(1))/100.0

        dead_end_states_match = re.search("Dead-end states:\s+([0-9\.]*)%", output)
        if dead_end_states_match:
            torchlight_features['torchlight-deadEndPercentage'] = float(dead_end_states_match.group(1))/100.0

        exit_distance_match = re.search("Exit distance bound min:\s+([0-9\.\-]*), mean:\s+([0-9\.\-]*), max:\s+([0-9\.\-]*)", output)
        if exit_distance_match:
            torchlight_features['torchlight-exitDistanceMin'] = float(exit_distance_match.group(1))
            torchlight_features['torchlight-exitDistanceMean'] = float(exit_distance_match.group(2))
            torchlight_features['torchlight-exitDistanceMax'] = float(exit_distance_match.group(3))

        action_templates_match = re.search("instantiating ([0-9]*) easy, ([0-9]*) hard action templates", output)
        if action_templates_match:
            torchlight_features['torchlight-easyActionTemplates'] = float(action_templates_match.group(1))
            torchlight_features['torchlight-hardActionTemplates'] = float(action_templates_match.group(2))

        facts_actions_match = re.search("yielding ([0-9]*) facts and ([0-9]*) actions", output)
        if facts_actions_match:
            torchlight_features['torchlight-reachabilityFacts'] = float(facts_actions_match.group(1))
            torchlight_features['torchlight-reachabilityActions'] = float(facts_actions_match.group(2))

        relevant_facts_match = re.search("representation with ([0-9]*) relevant facts", output)
        if relevant_facts_match:
            torchlight_features['torchlight-relevantFacts'] = float(relevant_facts_match.group(1))

        return torchlight_features
