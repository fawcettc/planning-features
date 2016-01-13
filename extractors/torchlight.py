#!/usr/bin/env python2.7
# encoding: utf-8
'''
    Copyright (C) 2013-2016 Chris Fawcett (fawcettc@cs.ubc.ca)

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

from feature_extractor import FeatureExtractor

import os
import sys
import re
import shutil

class TorchlightFeatureExtractor(FeatureExtractor):
    def __init__(self, args):
        super(TorchlightFeatureExtractor, self).__init__(args)

        self.extractor_name = "torchlight"

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

        path_to_translate  = "%s/torchlight/GENERATE-VARS/translate/translate.py" % self.abs_script_directory
        translate_command = ["python", path_to_translate, domain_path, instance_path]

        path_to_torchlight = "%s/torchlight/torchlight" % (self.abs_script_directory)
        torchlight_command = [path_to_torchlight, "-o", domain_path, "-f", instance_path, "-s", "100", "-V", "-v", "./output.sas"]

        successful = False

        try:
            output_directory = self.execute_command_with_runsolver(translate_command, None, None)

            sas_path = "%s/output.sas" % (output_directory)

            if os.path.exists(sas_path) and os.path.isfile(sas_path):
                self.execute_command_with_runsolver(torchlight_command, output_directory, None)

                with open("%s/cmd.stdout" % (output_directory), 'r') as f:
                    output = f.read()

                    torchlight_features = self.extract_features(output)
                    features.update(torchlight_features)

                    # make sure at least one non-sentinel value, otherwise obviously not successful
                    for key,value in features.iteritems():
                        if value != self.sentinel_value:
                            successful = True
        except Exception as e:
            print "Exception running Torchlight: %s" % (str(e))
        finally:
            shutil.rmtree(output_directory)

        return successful,features

    def extract_features(self, output):
        torchlight_features = {}
        print "torchlight output %s" % output

        success_percentage_match = re.search("Perc successful gDG\s+:\s+([0-9\.]*)\s+\/\*", output)
        if success_percentage_match:
            torchlight_features['torchlight-successPercentage'] = float(success_percentage_match.group(1))/100.0

        dead_end_states_match = re.search("Perc dead end states\s+:\s+([\-0-9\.]*)", output)
        if dead_end_states_match:
            match = dead_end_states_match.group(1)
            if match == "-2147483648":
                torchlight_features['torchlight-deadEndPercentage'] = -1.0
            else:
                torchlight_features['torchlight-deadEndPercentage'] = float(match)/100.0

        exit_distance_match = re.search("h\+ exit distance bound\s+:\s+([0-9\.\-]*),\s+([0-9\.\-]*),\s+([0-9\.\-]*) \/\* min, mean, max over successful gDGs", output)
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
