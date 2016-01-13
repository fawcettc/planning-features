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

import os
import sys
from subprocess import Popen, PIPE
import tempfile

class FeatureExtractor(object):
    '''
        abstract feature extractor
    '''
    def __init__(self, args):
        self.memory_limit = args.mem_limit
        self.runtime_limit = args.per_extraction_time_limit
        self.runsolver_path = args.runsolver
        self.abs_script_directory = os.path.abspath(os.path.dirname(sys.argv[0]))

        # for creating/maintaining a shared directory with the SAS+ representation
        self.creates_sas_representation = False
        self.requires_sas_representation = False

        self.sentinel_value = "-512.0"

        self.extractor_name = "BASE EXTRACTOR"

    '''
    '''
    def extract(self, domain_path, instance_path):
        print "ERROR: You should have written a new extract() for your feature extractor"
        return False,{}

    '''
    '''
    def default_features(self):
        print "ERROR: You need to provide default_features for your feature extractor"
        return {}

    '''
    '''
    def execute_command_with_runsolver(self, command, temporary_directory=None, stdin_file=None, runtime_limit=None):
        try:
            if temporary_directory == None:
                temporary_directory = tempfile.mkdtemp(prefix='pfeat.',suffix='.tmp')

            runsolver_stdout = "%s/runsolver.stdout" % (temporary_directory)
            cmd_stdout = "%s/cmd.stdout" % (temporary_directory)

            if runtime_limit == None:
                runtime_limit = self.runtime_limit

            modified_cmd = [self.runsolver_path, "-w", runsolver_stdout, "-o", cmd_stdout, "-C", runtime_limit, "-M", self.memory_limit, "-d", "2"]
            modified_cmd.extend(command)

            if stdin_file != None:
                stdin_file = open(stdin_file, 'r')

            io = Popen(map(str, modified_cmd), shell=False, preexec_fn=os.setpgrp, cwd=temporary_directory, stdin=stdin_file)
            io.wait()
        except Exception as e:
            print "ERROR: Exception during feature extraction: %s" % (str(e))
        except:
            print "ERROR: Unknown exception during feature extraction!"
        finally:
            if stdin_file != None:
                stdin_file.close()

        return temporary_directory
