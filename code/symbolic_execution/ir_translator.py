import os
import sys
import copy
import json
import re

# (notice)
# 1. Back slashes \ will automatically be processed and removed by the json library. E.g., 
#    "TMP_64 = TMP_63 \/ refund_contract_eth_value" --> "TMP_64 = TMP_63 / refund_contract_eth_value"
# 2. call_rewrite should come before type_alias
class IRTranslator(object):
	def __init__(self):
		self.full_translate_sequence = [
			# ==== (notice) santa mode ==== #
			# "santa_internal_call",
			# ==== (notice) santa mode ==== #

			# (important) the order is strict, don't change
			"json_formatter",
			"unify_assignment", 
			# ====
			"high_level_call_rewrite",
			"low_level_call_rewrite",
			"send_rewrite",
			"transfer_rewrite",
			"recipe_rewrite",
			# ====
			"type_alias", # done
			"nop_alias",  # done
			"require_split",  # done
			"convert_rewrite",  # done
			"correct_types", # done
			"builtin_structs", # done
			"clean_range_variables", # done
			"this_to_address",
			"fix_balance_this_address", 
			# ==== ???? ====
			"enum_formalization",
			# ====
			# other translations can generate complex expressions, which will be rewritten here
			# (notice): these two unwrap functions should be applied together
			"unnest_term",
			"unwrap_instruction",
			# ====
			"complex_new_cv",
			# ====
			"special_rule_0",

			"arrU_LHS_expansion",
			# ==== (notice) santa mode ==== #

			# ==== (notice) santa mode ==== #
			"fill_in_nop_for_zero_len",
		]
		self.ins_count = 0 # helper for "clean_instruction_terms"
		self.wrp_count = 0 # helper for "unwrap_instruction"
		self.ncv_count = 0 # helper for "complex_new_cv"
		self.spl_count = 0 # helper for special rules

		self.alias_dict = { "mapping": "array", "address": "integer", "bool": "boolean", "uint": "integer", "int": "integer", "byte": "integer", "bytes": "integer" }
		for i in range(8,256+1,8):
			self.alias_dict["uint{}".format(i)] = "integer"
			self.alias_dict["int{}".format(i)] = "integer"

		for i in range(1,32+1):
			self.alias_dict["bytes{}".format(i)] = "integer"
		# replace string type with unknown
		self.alias_dict["string"] = "unknown"

		pass

	def get_fresh_wrp(self):
		tmp_wrp = "WRP_{}".format(self.wrp_count)
		self.wrp_count += 1
		return tmp_wrp

	def get_fresh_ncv(self):
		tmp_ncv = "NCV_{}".format(self.ncv_count)
		self.ncv_count += 1
		return tmp_ncv

	def get_fresh_spl(self):
		tmp_spl = "SPL_{}".format(self.spl_count)
		self.spl_count += 1
		return tmp_spl

	def translate(self, original_json, translate_sequence=None):
		# init
		self.ins_count = 0
		self.wrp_count = 0
		self.ncv_count = 0
		self.spl_count = 0

		new_json = copy.deepcopy(original_json)
		# since the target is a dictionary, all operations are in-place operations
		if translate_sequence is None:
			# use the pre-defined full sequence
			translate_sequence = self.full_translate_sequence
		# apply the translations one by one
		for tname in translate_sequence:
			_m = getattr(self, "_t_{}".format(tname))
			_m(new_json)
		return new_json

	# json pre-checker and re-formatter, will:
	# 1. wrap value into a list if that field should be a list, e.g., "init": "0xe" should be "init": ["0xe"]
	def _t_json_formatter(self, json_obj):

		def do_format(obj):
			if isinstance(obj, dict):
				for dkey in obj.keys():
					if dkey in ["type", "init", "instructions", "addrs"]:
						if not isinstance(obj[dkey], list):
							obj[dkey] = [obj[dkey]]
					else:
						do_format(obj[dkey])
			elif isinstance(obj, list):
				for i in range(len(obj)):
					do_format(obj[i])
			else:
				return

		do_format(json_obj)

	# the checker doesn't tell different assignment/reference type any more
	# also there are some misuse of those operators
	# so here we unify ":="/"="/"->" all to "="
	def _t_unify_assignment(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					dblk["instructions"][j] = dblk["instructions"][j].replace(" := ", " = ")
					dblk["instructions"][j] = dblk["instructions"][j].replace(" -> ", " = ")

	# ref: https://solidity.readthedocs.io/en/v0.5.3/types.html
	# treat string type as unknown type 
	# (notice that unknown type is a conditional type that can be either boolean or integer)
	def _t_type_alias(self, json_obj):

		# in-place operation, recursively
		def do_type_alias(olist):
			for i in range(len(olist)):
				if isinstance(olist[i],list):
					do_type_alias(olist[i])
				elif olist[i] in self.alias_dict.keys():
					olist[i] = self.alias_dict[olist[i]]

		# structs
		for i in range(len(json_obj["global_structs"])):
			dstruct = json_obj["global_structs"][i]
			for dfield in dstruct["fields"].keys():
				do_type_alias(dstruct["fields"][dfield])

		# variables
		for b in ["global_variables"]:
			for i in range(len(json_obj[b])):
				dvar = json_obj[b][i]
				do_type_alias(dvar["type"])

		# blocks/instructions
		# only recognize NEW_VAL type and NEW_COL type
		# because other occurences of type are invalid
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					for dkey in self.alias_dict.keys():
						kw_val = r"NEW_VAL {}$".format(dkey)
						rs_val = re.search(kw_val, dblk["instructions"][j].strip())
						if rs_val is not None:
							dblk["instructions"][j] = dblk["instructions"][j].replace("NEW_VAL {}".format(dkey), "NEW_VAL {}".format(self.alias_dict[dkey]))

						kw_col = r"NEW_COL {}$".format(dkey)
						rs_col = re.search(kw_col, dblk["instructions"][j].strip())
						if rs_col is not None:
							dblk["instructions"][j] = dblk["instructions"][j].replace("NEW_COL {}".format(dkey), "NEW_COL {}".format(self.alias_dict[dkey]))

	# convert the following instructions to NOP
	# ENTRY_POINT ??
	# END_IF ??
	# BEGIN_LOOP ?
	# END_LOOP ?
	# Emit
	# RETURN ?
	# NEW VARIABLE None
	# DESTINATION
	# PUSH ?? in ??
	# EXPRESSION ??
	# selfdestruct(
	# SOLIDITY_CALL revert(
	# THROW ??
	# INLINE
	def _t_nop_alias(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					if "ENTRY_POINT " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "BEGIN_LOOP " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "END_LOOP " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "END_IF " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "Emit " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "RETURN " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "NEW VARIABLE None" in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "_ None" in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "DESTINATION" in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "PUSH " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "EXPRESSION " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "selfdestruct(" in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "SOLIDITY_CALL revert(" in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "THROW " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"
					if "INLINE " in dblk["instructions"][j]:
						dblk["instructions"][j] = "NOP"

	# split a block that contains `require` into 3 blocks
	# this also deals with `assert`
	# only process normal blocks
	def _t_require_split(self, json_obj):
		tmp_block_require_trap = {
			"scope": "RequireTrap",
			"addr": "0xRequireTrap",  # no problem, greg models address as string
			"instructions": [
				"NOP"
			]
		}

		# extra flag to determine whether or not to add the require block
		hasRequire = False

		# for block_type in ["normal_blocks"]:
		for block_type in ["normal_blocks", "range_blocks"]:
			new_block_collection = []
			for i in range(len(json_obj[block_type])):
				block_template = copy.deepcopy(json_obj[block_type][i])
				block_template["instructions"] = []
				addr_template = json_obj[block_type][i]["addr"]
				new_blocks = [copy.deepcopy(block_template)]
				block_ptr = 0
				for j in range(len(json_obj[block_type][i]["instructions"])):
					if "SOLIDITY_CALL require(" in json_obj[block_type][i]["instructions"][j]:
						# should add the require trap at the end
						hasRequire = True

						# extract the required variables
						exv = re.search(r"SOLIDITY_CALL require\(.*?\)\((.*?)\)", json_obj[block_type][i]["instructions"][j]).groups()
						assert len(exv)==1, "_t_require_split: require match failed, original string: {}".format(json_obj[block_type][i]["instructions"][j])

						new_block_addr = "{}_r{}".format(addr_template, block_ptr)
						argument = exv[0].split(",")[0]
						new_blocks[block_ptr]["instructions"].append("CONDITION {} {} 0xRequireTrap".format(argument, new_block_addr))
						
						new_blocks.append(copy.deepcopy(block_template))
						block_ptr += 1
						new_blocks[block_ptr]["addr"] = new_block_addr
					elif "SOLIDITY_CALL assert(" in json_obj[block_type][i]["instructions"][j]:
						# should add the require trap at the end
						hasRequire = True

						# extract the required variables
						exv = re.search(r"SOLIDITY_CALL assert\(.*?\)\((.*?)\)", json_obj[block_type][i]["instructions"][j]).groups()
						assert len(exv)==1, "_t_require_split: require match failed, original string: {}".format(json_obj[block_type][i]["instructions"][j])

						new_block_addr = "{}_r{}".format(addr_template, block_ptr)
						argument = exv[0].split(",")[0]
						new_blocks[block_ptr]["instructions"].append("CONDITION {} {} 0xRequireTrap".format(argument, new_block_addr))
						
						new_blocks.append(copy.deepcopy(block_template))
						block_ptr += 1
						new_blocks[block_ptr]["addr"] = new_block_addr
					else:
						new_blocks[block_ptr]["instructions"].append(json_obj[block_type][i]["instructions"][j])
				# then put all the blocks
				for p in new_blocks:
					new_block_collection.append(p)
			# then update the block collection
			json_obj[block_type] = new_block_collection

		# add an additional block
		if hasRequire:
			json_obj["normal_blocks"].append(tmp_block_require_trap)

	# contract:
	# HIGH_LEVEL_CALL is the same as NEW_VAL type, 
	# the type is determined from the call; 
	# if the call is malformed, it will be modeled as NEW_VAL unknown (if type can't be inferred, NOP it out)
	# https://github.com/crytic/slither/blob/master/slither/slithir/operations/high_level_call.py
	def _t_high_level_call_rewrite(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					if "HIGH_LEVEL_CALL" in dblk["instructions"][j]:
						rrs = re.search(r"(.*?)\((.*?)\) = HIGH_LEVEL_CALL, .*", dblk["instructions"][j])
						if rrs is None:
							# assert False, "malformed HIGH_LEVEL_CALL, got: {}".format(dblk["instructions"][j])
							dblk["instructions"][j] = "NOP"
						else:
							exv = rrs.groups()
							if len(exv[1].split(","))>1:
								# it's a tuple with >=2 types, use unknown directly

								dblk["instructions"][j] = "{} = NEW_COL unknown".format(exv[0])
							else:
								dblk["instructions"][j] = "{} = NEW_VAL {}".format( exv[0], self.alias_dict.get(exv[1], "unknown") )

	# contract:
	# LOW_LEVEL_CALL subtracts value from this.balance, and returns NEW_VAL type where type is determined from the call; 
	# if the call is malformed, it will be modeled as NEW_VAL unknown (if type can't be inferred, NOP it out)
	# https://github.com/crytic/slither/blob/master/slither/slithir/operations/low_level_call.py
	def _t_low_level_call_rewrite(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				tmp_instructions = []
				for j in range(len(dblk["instructions"])):
					if "LOW_LEVEL_CALL" in dblk["instructions"][j]:
						# first try to detect "value" argument

						rrs = re.search(r"(.*?)\((.*?)\) = LOW_LEVEL_CALL, .*value:(.*?) ", dblk["instructions"][j])
						if rrs is None:
							# no "value" argument is found, then just detect the call
							rrs0 = re.search(r"(.*?)\((.*?)\) = LOW_LEVEL_CALL, .*", dblk["instructions"][j])
							if rrs0 is None:
								# assert False, "malformed LOW_LEVEL_CALL, got: {}".format(dblk["instructions"][j])
								tmp_instructions.append( "NOP" )
							else:
								exv0 = rrs0.groups()
								if len(exv0[1].split(","))>1:
									# it's a tuple with >=2 types, use unknown directly

									tmp_instructions.append( "{} = NEW_COL unknown".format(exv0[0]) )
								else:
									tmp_instructions.append( "{} = NEW_VAL {}".format(exv0[0], self.alias_dict.get(exv0[1], "unknown") ) )

						else:
							# perform more sophisticated instructions
							exv = rrs.groups()
							tmp_instructions.append( "this.balance = this.balance - {}".format(exv[2]) )
							if len(exv[1].split(","))>1:
								# it's a tuple with >=2 types, use unknown directly
								tmp_instructions.append( "{} = NEW_COL unknown".format(exv[0]) )
							else:
								tmp_instructions.append( "{} = NEW_VAL {}".format(exv[0], self.alias_dict.get(exv[1], "unknown") ) )
					else:
						tmp_instructions.append( dblk["instructions"][j] )

				# replace the isntruction list
				dblk["instructions"] = tmp_instructions

	# SEND will be modeled the same way as LOW_LEVEL_CALL
	def _t_send_rewrite(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				tmp_instructions = []
				for j in range(len(dblk["instructions"])):
					if "SEND" in dblk["instructions"][j]:
						# first try to detect "value" argument
						# rrs = re.search(r"(.*?)\((.*?)\) = SEND .*value:(.*?)", dblk["instructions"][j])
						# (notice) for SEND, there's no type attached
						rrs = re.search(r"(.*?) = SEND .*value:(.*?)$", dblk["instructions"][j])
						if rrs is None:
							# no "value" argument is found, then just detect the call
							rrs0 = re.search(r"(.*?) = SEND .*", dblk["instructions"][j])
							if rrs0 is None:
								# assert False, "malformed SEND, got: {}".format(dblk["instructions"][j])
								tmp_instructions.append( "NOP" )
							else:
								exv0 = rrs0.groups()
								tmp_instructions.append( "{} = NEW_VAL unknown".format(exv0[0]) )
						else:
							# perform more sophisticated instructions
							exv = rrs.groups()
							tmp_instructions.append( "this.balance = this.balance - {}".format(exv[1]) )
							tmp_instructions.append( "{} = NEW_VAL unknown".format(exv[0]) )
					else:
						tmp_instructions.append( dblk["instructions"][j] )

				# replace the isntruction list
				dblk["instructions"] = tmp_instructions

	# contract:
	# Transfer subtracts value from this.balance, and returns nothing; 
	# if no value is given, it's modeled as NOP
	# https://github.com/crytic/slither/blob/master/slither/slithir/operations/transfer.py
	def _t_transfer_rewrite(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				tmp_instructions = []
				for j in range(len(dblk["instructions"])):
					# Transfer should be at the very beginning, don't modify this regex
					# if "Transfer" in dblk["instructions"][j]:
					ttt = re.search(r"^Transfer", dblk["instructions"][j].strip())
					if ttt is not None:
						# first try to detect "value" argument
						# (notice) the pattern is "value:(.*)" without space at the end, see the source code of slither
						rrs = re.search(r"value:(.*)", dblk["instructions"][j])
						if rrs is None:
							# no "value" argument is found, then just NOP out
							tmp_instructions.append( "NOP" )
						else:
							# perform more sophisticated instructions
							exv = rrs.groups()
							tmp_instructions.append( "this.balance = this.balance - {}".format(exv[0]) )
					else:
						tmp_instructions.append( dblk["instructions"][j] )

				# replace the isntruction list
				dblk["instructions"] = tmp_instructions

	# rewrite CONVERT ?? TO ?? to assignment
	def _t_convert_rewrite(self, json_obj):
		for block_type in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[block_type])):
				for j in range(len(json_obj[block_type][i]["instructions"])):
					inst_tokens = json_obj[block_type][i]["instructions"][j].split(" ")
					if "CONVERT" in inst_tokens:
						exv = re.search(r"(.*?) = CONVERT (.*?) to .*?", json_obj[block_type][i]["instructions"][j]).groups()
						assert len(exv)==2, "_t_convert_rewrite: convert match failed, original string: {}".format(json_obj[block_type][i]["instructions"][j])

						json_obj[block_type][i]["instructions"][j] = "{} = {}".format(exv[0], exv[1])

	# 1. remove brackets of internal single type (if there's any)
	#    e.g., ["array", "integer", ["tokenInv"]]
	def _t_correct_types(self, json_obj):
		def unwrap(dlist, keep):
			if isinstance(dlist, list):
				if len(dlist)==0:
					return None
				elif len(dlist)==1:
					if keep:
						return dlist
					else:
						return dlist[0]
				else:
					for i in range(len(dlist)):
						tmp = unwrap(dlist[i], False)
						if tmp is None:
							continue
						else:
							dlist[i] = tmp
					return dlist
			else:
				return dlist
			
		for dfield in ["global_variables"]:
			for i in range(len(json_obj[dfield])):
				original_type = json_obj[dfield][i]["type"]
				json_obj[dfield][i]["type"] = unwrap(original_type, True)


	# add builtin structs and corresponding global variables (msg, block, tx)
	# currently this is constructed dynamically (by detecting a.b patterns)
	# specific steps are:
	# 1. detect for "a.b" patterns
	# 2. create new struct "struct_a" (in global_structs)
	# 3. make "b" a field in "struct_a" (in global_structs)
	# 4. make "a" an instance of "struct_a" (in global_variables, after finding all "a.b" patterns)
	# 5. combine all the init blocks and don't modify
	# (notice: only deal with a.b pattern, if there's a.b.c, will throw exception)
	def _t_builtin_structs(self, json_obj):
		new_global_structs = {} # this will have to be translated to list eventually
		new_global_variables = {} # this will have to be translated to list eventually
		for i in range(len(json_obj["global_variables"])):
			vblock = json_obj["global_variables"][i]
			vname = vblock["name"]
			vtype = vblock["type"]
			vinit = vblock["init"]
			if "." in vname:

				# there's an "a.b" pattern
				tmp = vname.split(".")
				assert len(tmp)==2, "unsupported identifier pattern, got: {}".format(vname)

				# assemble new struct
				vstruct = "struct_{}".format(tmp[0])
				vinstance = tmp[0]
				vfield = tmp[1]

				if vstruct not in new_global_structs.keys():
					new_global_structs[vstruct] = {}
				if vfield not in new_global_structs[vstruct].keys():
					new_global_structs[vstruct][vfield] = None
				# over-write the existing type (if there's already any), don't check
				new_global_structs[vstruct][vfield] = vtype

				# assemble new variable
				if vinstance not in new_global_variables.keys():
					new_global_variables[vinstance] = {
						"type": [vstruct],
						"init": vinit,
					}
				else:
					assert new_global_variables[vinstance]["type"] == [vstruct]
					new_global_variables[vinstance]["init"] += vinit # add more init

			else:
				# no pattern found
				new_global_variables[vname] = {
					"type": vtype,
					"init": vinit,
				}

		# finally convert the data structures to list
		list_global_structs = [
			{
				"name": dname,
				"fields": {
					dfield: new_global_structs[dname][dfield]
					for dfield in new_global_structs[dname].keys()
				}
			}
			for dname in new_global_structs.keys()
		]
		list_global_variables = [
			{
				"name": dname,
				"type": new_global_variables[dname]["type"],
				"init": new_global_variables[dname]["init"],
			}
			for dname in new_global_variables.keys()
		]

		# update the original json
		json_obj["global_structs"] += list_global_structs # add new global structs
		json_obj["global_variables"] = list_global_variables # re-write variables

	# only keep the top level identifiers of the range variables
	# e.g., "tokens.user" will become "tokens" only
	# e.g., a[b.d].c will become a
	# see the specifications for explanations about this mechanism
	def _t_clean_range_variables(self, json_obj):
		for i in range(len(json_obj["range_variables"])):
			rblock = json_obj["range_variables"][i]
			rname = rblock["name"]
			tmp = re.split("\.|\[|\]", rname)[0]
			# replace the name
			json_obj["range_variables"][i]["name"] = tmp

	# re-format the terms in the instruction
	# e.g., "userInventory[msg.sender][U].workDone := U" will become
	# CLR_0 -> msg.sender
	# CLR_1 -> userInventory[CLR_0]
	# CLR_2 -> CLR_1[U]
	# CLR_2.workDone := U
	# e.g., "REF_21 -> userInventory[msg.sender]" will become
	# CLR_0 -> msg.sender
	# REF_21 -> userInventory[CLR_0]
	# ------
	# notice that the semantic explanation of U here may change
	# assume the instruction is gramatically correct
	def _t_unnest_term(self, json_obj):
		# clean a single instruction's left-hand-side
		# dterm should be pre-processed (by adding extra spaces)
		# n: how many to preserve in the list, usually 2 for the outer-most layer, 1 for the inner layers
		def do_clean(dtokens, dlst, n):
			# print("# get tokens: {}".format(dtokens))
			reduced_tokens = []
			tmp_stack = []
			tmp_tokens = []
			for i in range(len(dtokens)):
				p = dtokens[i]
				if p==".":
					if len(tmp_stack)>0:
						tmp_tokens.append(p)
					else:
						continue
				elif p=="[":
					tmp_stack.append(p)
					if len(tmp_stack)>1:
						tmp_tokens.append(p)
				elif p=="]":
					if len(tmp_stack) > 0:
						tmp_stack.pop()

					if len(tmp_stack)>0:
						tmp_tokens.append(p)
					else:
						reduced_tokens.append(
							( do_clean(tmp_tokens, dlst, 1), "b" )
						)
						tmp_tokens = []
				else:
					if len(tmp_stack)>0:
						tmp_tokens.append(p)
					else:
						reduced_tokens.append( (p, "d") )
			while len(reduced_tokens)>n:
				tmp0 = reduced_tokens.pop(0)
				tmp1 = reduced_tokens.pop(0)
				assert tmp0[1]=="d"
				if tmp1[1]=="d":
					dlst.append("CLR_{} = {}.{}".format(self.ins_count, tmp0[0], tmp1[0]))
				else:
					dlst.append("CLR_{} = {}[{}]".format(self.ins_count, tmp0[0], tmp1[0]))
				tmp2 = ("CLR_{}".format(self.ins_count), "d")
				self.ins_count += 1
				reduced_tokens = [tmp2] + reduced_tokens
			if len(reduced_tokens)==1:
				return reduced_tokens[0][0]
			else:
				tmpr = ""
				for i in range(len(reduced_tokens)):
					if i==0:
						assert reduced_tokens[i][1]=="d"
						tmpr += reduced_tokens[i][0]
					else:
						if reduced_tokens[i][1]=="d":
							tmpr += ".{}".format(reduced_tokens[i][0])
						else:
							tmpr += "[{}]".format(reduced_tokens[i][0])
				return tmpr

		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblock = json_obj[b][i]
				dinsts = dblock["instructions"]
				new_insts = []
				for j in range(len(dinsts)):
					dcomps = dinsts[j].split(" ")

					# lhs
					for k in range(len(dcomps)):
						tmp_insts = []
						dready = dcomps[k].replace(".", " . ").replace("[", " [ ").replace("]", " ] ").split(" ")
						dready = [p for p in dready if len(p)>0]
						if k==0:
							# print("# cleaning {}".format(dready))
							new_lhs = do_clean(dready, tmp_insts, 2)
						else:
							# rhs should reduce to 1
							# e.g., TMP_0 = 1 + a.b is not allowed
							# print("# cleaning {}".format(dready))
							new_lhs = do_clean(dready, tmp_insts, 1)
						new_insts += tmp_insts
						dcomps[k] = new_lhs

					new_insts.append(" ".join(dcomps))
				dblock["instructions"] = new_insts

	# this unwrap instruction into valid forms (that the IR allows)
	# e.g., this.balance = this.balance - TMP_0
	# will be:
	# CLR_0 = this.balance
	# CLR_1 = CLR_0 - TMP_0
	# this.balance = CLR_1
	def _t_unwrap_instruction(self, json_obj):

		def detect_pattern(ptokens):
			# pattern for instruction rewrite
			# assignment: 0, operator:1, index/access:2, normal:3
			pp = []
			for i in range(len(ptokens)):
				if ptokens[i]=="=":
					pp.append(0)
				elif ptokens[i] in ["+", "-" ,"*", "/", "**", "%", "!", "&&", "||", "<", "<=", ">", ">=", "==", "!="]:
					pp.append(1)
				elif "." in ptokens[i] or "[" in ptokens[i]:
					pp.append(2)
				else:
					pp.append(3)
			return tuple(pp)

		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				tmp_instructions = []
				for j in range(len(dblk["instructions"])):
					dinst = dblk["instructions"][j].strip()
					dtokens = [p for p in dinst.split(" ") if len(p)>0]
					tmp_tokens = []
					tmp_insts = []
					dpat = detect_pattern(dtokens)
					operation_flags = {
						# pattern: (need_token_rewrite, need_instruction_rewrite)
						# need_token_rewrite: True if complex tokens in RHS
						# need_instruction_rewrite: True if complex tokens in LHS and contains operator
						# default: (False, False)

						(2,0,2): (True, False),
						(3,0,2): (False, False), # notice that not all complex tokens on RHS need rewriting
						(3,0,3): (False, False),

						(2,0,1,2): (True, True),
						(2,0,1,3): (False, True),
						(3,0,1,2): (True, False),
						(3,0,1,3): (False, False),

						(2,0,2,1,2): (True, True),
						(2,0,2,1,3): (True, True),
						(2,0,3,1,2): (True, True),
						(2,0,3,1,3): (False, True),

						(3,0,2,1,2): (True, False),
						(3,0,2,1,3): (True, False),
						(3,0,3,1,2): (True, False),
						(3,0,3,1,3): (False, False),

						# (notice) this is addressed in special_rule_0
						# e.g., RTMP_419 = ! REF_130 != 0
						# (2,0,1,2,1,2): (True, True),
					}
					dflags = operation_flags.get(dpat, (False, False))

					# first replace complex tokens (tokens that appear on the rhs)
					if dflags[0]:
						for k in range(len(dtokens)):
							if k==0:
								# safely assume that register to store is always at pos=0
								tmp_tokens.append(dtokens[k])
							else:
								if "." in dtokens[k] or "[" in dtokens[k]:
									tmp_name = self.get_fresh_wrp()
									tmp_insts.append( "{} = {}".format(tmp_name, dtokens[k]) )
									tmp_tokens.append(tmp_name)
								else:
									tmp_tokens.append(dtokens[k])
					else:
						tmp_tokens = dtokens

					# then rewrite complex expression
					if dflags[1]:
						if len(dpat)==5:
							# binary op
							# a.b = c + d, should split into two instructions
							tmp_name = self.get_fresh_wrp()
							tmp_insts.append( "{} = {} {} {}".format(tmp_name, tmp_tokens[2], tmp_tokens[3], tmp_tokens[4]) )
							tmp_insts.append( "{} = {}".format(tmp_tokens[0], tmp_name) )
						elif len(dpat)==4:
							# unary op
							# a.b = !d, should split into two instructions
							tmp_name = self.get_fresh_wrp()
							tmp_insts.append( "{} = {} {}".format(tmp_name, tmp_tokens[2], tmp_tokens[3]) )
							tmp_insts.append( "{} = {}".format(tmp_tokens[0], tmp_name) )
						else:
							assert False, "unreachable path"
					else:
						# no need to split
						tmp_insts.append( " ".join(tmp_tokens) )
					# add the instructions
					tmp_instructions += tmp_insts
				# replace the instructions
				dblk["instructions"] = tmp_instructions

	# RTMP_419 = ! REF_130 != 0
	# converts to
	# SPL_0 = ! REF_130
	# RTMP_419 = SPL_0 != 0
	def _t_special_rule_0(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				new_instructions = []
				for j in range(len(dblk["instructions"])):
					inst_tokens = dblk["instructions"][j].split(" ")
					if len(inst_tokens)==6:
						if inst_tokens[1]=="=" and inst_tokens[2]=="!" and inst_tokens[4]=="!=":
							tmp_name = self.get_fresh_spl()
							new_instructions.append( "{} = {} {}".format(tmp_name, inst_tokens[2], inst_tokens[3]) )
							new_instructions.append( "{} = {} {} {}".format(inst_tokens[0], tmp_name, inst_tokens[4], inst_tokens[5]) )
						else:
							new_instructions.append(dblk["instructions"][j])
					else:
						new_instructions.append(dblk["instructions"][j])
				dblk["instructions"] = new_instructions

	# make Recipe unknown
	# e.g., TMP_25 = new Recipe(id,itemId,clothRequired,woodRequired,metalRequired)
	# will be made: TMP_25 = NEW_VAL unknown
	def _t_recipe_rewrite(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					if " = new Recipe(" in dblk["instructions"][j]:
						tmp = dblk["instructions"][j].split(" = ")
						dblk["instructions"][j] = "{} = NEW_VAL unknown".format(tmp[0])

	# translate global_enums to global_structs, and attach initialization code to the var declared
	# enum is struct with initialization, and the instance is only one
	def _t_enum_formalization(self, json_obj):

		def detect_type(ttp):

			# (important) https://stackoverflow.com/questions/37888620/comparing-boolean-and-int-using-isinstance
			if type(ttp) is int:
				return "integer"
			elif type(ttp) is bool:
				return "boolean"
			else:
				assert False, "unsupported type, got: {}".format(ttp)

		for i in range(len(json_obj["global_enums"])):

			denum = json_obj["global_enums"][i]
			dname = denum["name"]
			dvalues = denum["values"]
			new_struct = {
				"name": "struct_{}".format(dname),
				"fields": {
					p: [detect_type(dvalues[p])] for p in dvalues.keys()
				}
			}
			# add to structs, put at the very first pos
			json_obj["global_structs"] = [new_struct] + json_obj["global_structs"]

			# add the only instance to global variables and attach initializations
			new_var = {
				"name": dname,
				"type": ["struct_{}".format(dname)],
				"init": ["0xEnumInit_{}".format(dname)],
			}
			json_obj["global_variables"] = [new_var] + json_obj["global_variables"]

			# construct initialization block in global blocks
			new_block = {
				"scope": "__GLOBAL__",
				"addr": "0xEnumInit_{}".format(dname),
				"instructions": [
					"{}.{} = {}".format(dname, dk, dvalues[dk])
					for dk in dvalues.keys()
				],
			}
			json_obj["global_blocks"] = [new_block] + json_obj["global_blocks"]

		# done, delete the field
		del json_obj["global_enums"]

	# split instruction that has indexing/access and NEW_COL/NEW_VAL apart
	# e.g., a.b = NEW_VAL integer
	# will be
	# NCV_0 = NEW_VAL integer
	# a.b = NCV_0
	def _t_complex_new_cv(self, json_obj):

		def detect_cv_pattern(obj):
			# 0: assignment, 1: indexing/access identifier, 2: NEW-x operator, 3: others
			tmp = [p for p in obj.split(" ") if len(p)>0]
			tmp_pat = []
			for i in range(len(tmp)):
				if tmp[i]=="=":
					tmp_pat.append(0)
				elif tmp[i]=="NEW_COL" or tmp[i]=="NEW_VAL":
					tmp_pat.append(2)
				elif "." in tmp[i] or "[" in tmp[i]:
					tmp_pat.append(1)
				else:
					tmp_pat.append(3)
			return tuple(tmp_pat)


		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				tmp_instructions = []
				for j in range(len(dblk["instructions"])):
					dinst = dblk["instructions"][j]
					dtokens = [p for p in dinst.split(" ") if len(p)>0]
					dpat = detect_cv_pattern(dinst)
					if dpat==(1,0,2,3):
						tmp_name = self.get_fresh_ncv()
						tmp_instructions.append( "{} = {} {}".format(tmp_name, dtokens[2], dtokens[3]) )
						tmp_instructions.append( "{} = {}".format(dtokens[0], tmp_name) )
					else:
						tmp_instructions.append(dinst)
				dblk["instructions"] = tmp_instructions

	# replace all single occurences of "this" to "this.address"
	def _t_this_to_address(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					inst_tokens = dblk["instructions"][j].split(" ")
					for k in range(len(inst_tokens)):
						if inst_tokens[k]=="this":
							inst_tokens[k] = "this.address"
					dblk["instructions"][j] = " ".join(inst_tokens)

	# replace all single occurences of "BALANCE this.address" to "BALANCE this"
	def _t_fix_balance_this_address(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					if dblk["instructions"][j]=="BALANCE this.address":
						dblk["instructions"][j] = "BALANCE this"
					elif dblk["instructions"][j].endswith("BALANCE this.address"):
						# ?? = BALANCE this.address
						dblk["instructions"][j] = dblk["instructions"][j].replace("BALANCE this.address", "BALANCE this")

	# expand arr[U] = ??? to multiple assignments to every element of arr
	# (notice) vlen is the default length of vector, which should match the vlen in solver
	def _t_arrU_LHS_expansion(self, json_obj, vlen=10):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				tmp_instructions = []
				for j in range(len(dblk["instructions"])):
					rrs = re.match(r"(.*?)\[U\] = (.*)", dblk["instructions"][j])
					if rrs is None:
						tmp_instructions.append(dblk["instructions"][j])
					else:
						exv = rrs.groups()
						if len(exv) != 2:
							assert False, "_t_arrU_LHS_expansion: malformed match, got: {}".format(dblk["instructions"][j])
						else:
							# expand
							for z in range(vlen):
								tmp_instructions.append("{}[{}] = {}".format(exv[0],z,exv[1]))
				dblk["instructions"] = tmp_instructions

	# fill in empty blocks with "NOP" placeholders, otherwise the checker will panic
	def _t_fill_in_nop_for_zero_len(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				if len(dblk["instructions"])==0:
					dblk["instructions"] = ["NOP"]

	# =============================== #
	# == rules only for santa mode == #
	# =============================== #

	def _t_santa_internal_call(self, json_obj):
		for b in ["global_blocks", "range_blocks", "normal_blocks"]:
			for i in range(len(json_obj[b])):
				dblk = json_obj[b][i]
				for j in range(len(dblk["instructions"])):
					if "INTERNAL_CALL" in dblk["instructions"][j]:
						rrs = re.search(r"(.*?)\((.*?)\) = INTERNAL_CALL, .*", dblk["instructions"][j])
						if rrs is None:
							assert False, "malformed INTERNAL_CALL, got: {}".format(dblk["instructions"][j])
							# dblk["instructions"][j] = "NOP"
						else:
							exv = rrs.groups()
							if len(exv[1].split(","))>1:
								# it's a tuple with >=2 types, use unknown directly
								dblk["instructions"][j] = "{} = NEW_COL unknown".format(exv[0])
							else:
								dblk["instructions"][j] = "{} = NEW_VAL {}".format(exv[0], exv[1])



if __name__ == "__main__":
	gt = IRTranslator()
	for dfile in sys.argv[1:]:
		print("# working on {}".format(dfile))

		with open(dfile, "r") as f:
			original_json = json.load(f)
		new_json = gt.translate(original_json)

		tmp_list = list(os.path.split(dfile))
		tmp_list[-1] = "greg.{}".format(tmp_list[-1]) # add g as a prefix to the file name
		tmp_path = os.path.join(*tmp_list)

		with open(tmp_path, "w") as f:
			json.dump(new_json, f, indent='\t')

	print("# all done.")
