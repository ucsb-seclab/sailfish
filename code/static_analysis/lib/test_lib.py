import sys
from printer import *
from storage import *


if __name__ == '__main__':
    if len(sys.argv) < 2:
        err('[Usage]: python test_lib.py <test_id>')
        sys.exit(1)
    test_id = int(sys.argv[1])

    if test_id == 1:
        file_hash_map = {}
        print(write_to_unique_file('/tmp', 'a.sol', 'AAX', file_hash_map, True))
        print(file_hash_map)
    
    elif test_id == 2:
        dir_hash_map = {}
        print(write_to_unique_directory('/tmp/src/f', '/tmp/dest', dir_hash_map, True))
        print(dir_hash_map)
