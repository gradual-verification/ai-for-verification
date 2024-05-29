this is the script for removing comment but reserve the specifications of the function by using the regular expression. 
It will run the removeProcess.py and process the .c file one by one in the input folder.
It also won't remove the predicate, lemma, and other things outside the function body.
To run, simply place all of the .c file into a folder and change the input_directory in x1.sh.
It will read all of the c file in the input directory and generate the output and store to the output directory with the _m.c suffix attached.
