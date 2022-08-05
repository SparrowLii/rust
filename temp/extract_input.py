import re
import os
import sys

mut_var_type_mapping = dict()
unmut_var_type_mapping = dict()
temp_var_user_var_name_mapping = dict()
closure_temp_var_mapping = dict()

# NOT THIS: fo = open("/Users/lichunmiao/rust/mir_dump/main.main.002-010.SimplifyCfg-elaborate-drops.after.mir", "r")

# fo = open("/Users/lichunmiao/trytry/liyuan.find_prime.001-001.SimplifyCfg-promote-consts.after.mir", "r")
mir_path = sys.argv[1]
fo = open(mir_path,"r")

str = fo.readlines()

for i in range(0, len(str)):
    line_str = str[i]
    matchObj = re.search( r'let mut (_\d+): (.+);', line_str)
    if matchObj:
        mut_var_type_mapping[matchObj.group(1)] = matchObj.group(2)
    
    matchObj = re.search( r'let (_\d+): (.+);', line_str)
    if matchObj:
        unmut_var_type_mapping[matchObj.group(1)] = matchObj.group(2)
    
    matchObj = re.search( r'debug (.+) => (.+);', line_str)
    if matchObj:
        temp_var_user_var_name_mapping[matchObj.group(2)] = matchObj.group(1)
        
    # find closure, e.g., [closure@03.rs:39:31: 39:42]
    matchObj = re.search( r'(_\d+): &\[closure(.+)\];', line_str)
    if matchObj:
        closure_temp_var_mapping[matchObj.group(2)] = matchObj.group(1) # 相同的key的value将会被替换
    
fo.close()

# folder_name = "/Users/lichunmiao/trytry/"
folder_name = sys.argv[2] #facts address

if not os.path.exists(folder_name+"mut_var_type_mapping.facts"):
    file1 = open(folder_name+"mut_var_type_mapping.facts", "a")
    for key,value in mut_var_type_mapping.items():
        print("\"{}\"\t{}".format(key, value),file=file1)
    
if not os.path.exists(folder_name+"unmut_var_type_mapping.facts"):
    file2 = open(folder_name+"unmut_var_type_mapping.facts", "a")
    for key,value in unmut_var_type_mapping.items():
        print("\"{}\"\t{}".format(key, value),file=file2)
    
if not os.path.exists(folder_name+"temp_var_user_var_name_mapping.facts"):
    file3 = open(folder_name+"temp_var_user_var_name_mapping.facts", "a")
    for key,value in temp_var_user_var_name_mapping.items():
        print("\"{}\"\t{}".format(key, value),file=file3)
    
if not os.path.exists(folder_name+"closure_temp_var_mapping.facts"):
    file4 = open(folder_name+"closure_temp_var_mapping.facts", "a")
    for key,value in closure_temp_var_mapping.items():
        print("\"{}\"\t\"{}\"".format(key, value),file=file4)
        
# 在function_call_point.facts中写自己需要查看的function point
# if not os.path.exists(folder_name+"function_call_point.facts"):
#     file5 = open(folder_name+"function_call_point.facts", "a")
#     print("\"Mid(bb7[6])\"",file=file5)











    
