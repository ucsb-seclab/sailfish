#!/usr/bin/python3

import os
import glob

def build(file_name):
    os.system('raco exe %s.rkt' % file_name)


if __name__ == '__main__':
    build('reentrancy')
    build('tod')
    build('tod-complement')
