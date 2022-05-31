import sys
sys.path.append("..")

import os
from lib import *

slither_operations = ['Assignment', 'Binary', 'Call', 'Condition', 'Delete', 'EventCall', 
                      'HighLevelCall', 'Index', 'InitArray', 'InternalCall', 'InternalDynamicCall', 
                      'LibraryCall', 'LowLevelCall', 'OperationWithLValue', 'Member', 'NewArray', 
                      'NewElementaryType', 'NewContract', 'NewStructure', 'Operation', 'Push', 
                      'Return', 'Send', 'SolidityCall', 'Transfer', 'TypeConversion', 
                      'Unary', 'Unpack', 'Length', 'Balance', 'Phi', 'PhiCallback', 'Nop']

solidity_types = ["ArrayType", "ElementaryType", "FunctionType", "MappingType", "UserDefinedType", "TypeInformation"]
DEBUG = 0
