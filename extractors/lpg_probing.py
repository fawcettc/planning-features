#!/usr/bin/env python2.7
# encoding: utf-8

from feature_extractor import FeatureExtractor

import os
import sys
import re
import shutil

class LPGProbingFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(LPGProbingFeatureExtractor, self).__init__(args)

        self.extractor_name = "lpg-probing"

    def default_features(self):
        base_features = [
            'lpgProbingNumActions',
            'lpgProbingNumConditionalActions',
            'lpgProbingNumFactsIndividual',
            'lpgProbingNumMutex',
            'lpgProbingNumOps',
            'lpgProbingNumFacts',
        ]

        defaults = { key : self.sentinel_value for key in base_features }

        return defaults

    def extract(self, domain_path, instance_path):
        features = self.default_features()

        path_to_lpg = "%s/lpg/lpg_pre" % (self.abs_script_directory)
        lpg_command = [path_to_lpg, "-o", domain_path, "-f", instance_path, "-n", "1"]

        successful = False

        try:
            output_directory = self.execute_command_with_runsolver(lpg_command, None, None)

            with open("%s/cmd.stdout" % (output_directory), 'r') as f:
                output = f.read()

                probing_features = self.extract_probing_features(output)
                features.update(probing_features)

                # make sure at least one non-sentinel value, otherwise obviously not successful
                for key,value in features.iteritems():
                    if value != self.sentinel_value:
                        successful = True
        except Exception as e:
            print "Exception running LPG: %s" % (str(e))
        finally:
            shutil.rmtree(output_directory)

        return successful,features

    def extract_probing_features(self, output):
        probing_features = {}

        num_actions_match = re.search("Number of actions\s+:\s+([0-9]*)", output)
        if num_actions_match:
            probing_features['lpgProbingNumActions'] = num_actions_match.group(1)

        num_conditional_actions_match = re.search("Number of conditional actions\s+:\s+([0-9]*)", output)
        if num_conditional_actions_match:
            probing_features['lpgProbingNumConditionalActions'] = num_conditional_actions_match.group(1)

        num_facts_match = re.search("Number of facts\s+:\s+([0-9]*)", output)
        if num_facts_match:
            probing_features['lpgProbingNumFactsIndividual'] = num_facts_match.group(1)

        mutex_match = re.search("total_ft_ft_mutex ([0-9]*) num_ops ([0-9]*) num_facts ([0-9]*)", output)
        if mutex_match:
            mutex = float(mutex_match.group(1))
            ops = float(mutex_match.group(2))
            facts = float(mutex_match.group(3))

            probing_features['lpgProbingNumMutex'] = mutex
            probing_features['lpgProbingNumOps'] = ops
            probing_features['lpgProbingNumFacts'] = facts

        return probing_features
