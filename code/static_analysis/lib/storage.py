import os
import sys
import glob
import json
import shutil
import hashlib
from .printer import *


# Given a file, return the content as a string
def read_file(file_path):
    with open(file_path, 'r') as fp:
        content = fp.read()
    return content


def check_if_file_exists(file):
    if os.path.isfile(file):
        return True
    else:
        err('File does not exist: %s' % file)
        return False


# Delete a file or directory in a robust way
def delete_path(path):
    try:
        # path could either be relative or absolute
        if os.path.isfile(path) or os.path.islink(path):
            os.remove(path)                             # Remove the file
        elif os.path.isdir(path):
            shutil.rmtree(path, ignore_errors=True)     # Remove the dir and all of its contents
        else:
            pass
    
    except:
        pass


# Read JSON configuration file
def read_config(config_file):
    config_file = config_file.strip()
    
    # File not provided
    if config_file is None or config_file == '':
        err('Configuration file not provided')
        sys.exit(1)

    # Read configuration file
    try:
        with open(config_file, 'r') as fp:
            config = json.load(fp)
    
    # File not found
    except FileNotFoundError as fnfe:
        err('Configuration file not found: %s' % config_file)
        sys.exit(1)
    
    # JSON malformed
    except json.decoder.JSONDecodeError as jde:
        err('Configuration JSON malformed: %s' % config_file)
        sys.exit(1)

    return config


def get_text_hash(text):
    text = text.replace('\r\n', '\n')
    text_hash = hashlib.md5(text.encode()).hexdigest()
    return text_hash


def save_to_disk(directory, contract_name, source_code, file_hash_map, save_file=True): 
    file_name = contract_name + '.sol'
    file_path = os.path.join(directory, file_name)
    file_index = 0
    does_file_exist = False
    is_existing = False
    new_source_hash = get_text_hash(source_code)

    # Is file_hash_map populated? If not, then store the
    # hashes of the files in the destination directory
    if len(file_hash_map) == 0:
        sol_file_regex = os.path.join(directory, '*.sol')
        for existing_contract_path in glob.glob(sol_file_regex):
            with open(existing_contract_path, 'r') as fp:
                existing_contract_source_code = fp.read()
            existing_contract_hash = get_text_hash(existing_contract_source_code)
            existing_contract_name = os.path.basename(existing_contract_path)
            file_hash_map[existing_contract_hash] = existing_contract_name

    # Look up the hash map to check if the same file exists already
    existing_file_name = file_hash_map.get(new_source_hash)
    if existing_file_name is not None:
        return existing_file_name, True      # is_existing = True

    # If the same file doesn't exist, even with some other name,
    # we store the file with its original name. In case of a name
    # collision, we append a numeric suffix: contract.sol => contract_xx.sol
    while True:
        does_file_exist = os.path.isfile(file_path)
        if does_file_exist:
            with open(file_path, 'r') as fp:
                existing_source = fp.read()

                existing_source_hash = hashlib.md5(existing_source.encode()).hexdigest()
                if new_source_hash == existing_source_hash:
                    is_existing = True
                    break

            # Form the file name with the next numeric prefix
            file_index += 1
            file_name = '%s_%d.sol' % (contract_name, file_index)
            file_path = os.path.join(directory, file_name)
        else:
            break
    
    # Update the file hash map
    file_hash_map[new_source_hash] = file_name

    if save_file:
        if not is_existing:
            with open(file_path, 'w') as fp:
                fp.write(source_code)
    
    return file_name, is_existing


def write_to_unique_file(directory, file_name, file_contents, file_hash_map, save_file=True):
    file_path_without_ext, ext = os.path.splitext(file_name)
    file_name_without_ext = os.path.basename(file_path_without_ext)
    file_path = os.path.join(directory, file_name)
    file_index = 0
    does_file_exist = False
    is_existing = False
    new_source_hash = get_text_hash(file_contents)

    # Is file_hash_map populated? If not, then store the
    # hashes of the files in the destination directory
    if len(file_hash_map) == 0:
        file_regex = os.path.join(directory, '*' + ext)
        for existing_file_path in glob.glob(file_regex):
            with open(existing_file_path, 'r') as fp:
                existing_file_contents = fp.read()
            existing_file_hash = get_text_hash(existing_file_contents)
            existing_file_name = os.path.basename(existing_file_path)
            file_hash_map[existing_file_hash] = existing_file_name

    # Look up the hash map to check if the same file exists already
    existing_file_name = file_hash_map.get(new_source_hash)
    if existing_file_name is not None:
        return existing_file_name, True      # is_existing = True

    # If the same file doesn't exist, even with some other name,
    # we store the file with its original name. In case of a name
    # collision, we append a numeric suffix: contract.sol => contract_xx.sol
    while True:
        does_file_exist = os.path.isfile(file_path)
        if does_file_exist:
            with open(file_path, 'r') as fp:
                existing_source = fp.read()

                existing_source_hash = hashlib.md5(existing_source.encode()).hexdigest()
                if new_source_hash == existing_source_hash:
                    is_existing = True
                    break

            # Form the file name with the next numeric prefix
            file_index += 1
            file_name = '%s_%d.sol' % (file_name_without_ext, file_index)
            file_path = os.path.join(directory, file_name)
        else:
            break
    
    # Update the file hash map
    file_hash_map[new_source_hash] = file_name

    if save_file:
        if not is_existing:
            with open(file_path, 'w') as fp:
                fp.write(file_contents)
    
    return file_name, is_existing


def get_dir_hash(directory):
    files = sorted(glob.glob(os.path.join(directory, '**'), recursive=True))
    files_merged = ''
    for file in files:
        if os.path.isfile(file):
            files_merged += read_file(file)
    dir_hash = get_text_hash(files_merged)
    return dir_hash


def write_to_unique_directory(src_dir, dest_dir, dir_hash_map, save_dir=True):
    src_dir_hash = get_dir_hash(src_dir)
    src_dir_name = os.path.basename(src_dir)

    # Is dir_hash_map populated? If not, then store the
    # hashes of the directories in the destination directory
    if len(dir_hash_map) == 0:
        files = glob.glob(os.path.join(dest_dir, '*'), recursive=False)
        for file in files:
            if os.path.isdir(file):
                dir_hash = get_dir_hash(file)
                dir_name = os.path.basename(file)
                dir_hash_map[dir_hash] = dir_name

    # Look up the hash map to check if the same directory exists already
    existing_dir_name = dir_hash_map.get(src_dir_hash)
    if existing_dir_name is not None:
        return existing_dir_name, True      # is_existing = True
    
    # If the same directory doesn't exist, even with some other name,
    # we store the directory with its original name. In case of a name
    # collision, we append a numeric suffix: AxY => AxY_nn
    dir_path = os.path.join(dest_dir, src_dir_name)
    dir_index = 0
    while True:
        does_dir_exist = os.path.isdir(dir_path)
        if does_dir_exist:
            # Form the directory name with the next numeric prefix
            dir_index += 1
            dir_name = '%s_%d' % (src_dir_name, dir_index)
            dir_path = os.path.join(dest_dir, dir_name)
        else:
            break
    
    # Update the directory hash map
    dir_hash_map[src_dir_hash] = dir_name

    if save_dir:
        shutil.move(src_dir, dir_path)
    
    return dir_name, False                  # is_existing = False
