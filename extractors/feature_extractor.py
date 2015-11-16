#!/usr/bin/env python2.7
# encoding: utf-8

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

    '''
    '''
    def extract(self, domain_path, instance_path):
        print "ERROR: You should have written a new extract() for your feature extractor"
        return {}

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
