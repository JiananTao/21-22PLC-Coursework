# 
# Rules for compiling and linking the typechecker/evaluator
#
# Type
#   make         to rebuild the executable files
#   make clean   to remove all intermediate and temporary files
#   

# Files that need to be generated from other files
DEPEND += StqlTokens.hs StqlGrammar.hs StqlEval.hs

# When "make" is invoked with no arguments, we build an executable 
#  after building everything that it depends on
all: $(DEPEND) Stql

# Build an executable for Stql interpreter
Stql: $(DEPEND) Stql.hs
	ghc Stql.hs

# Generate ML files from a parser definition file
StqlGrammar.hs : StqlGrammar.y
	@rm -f StqlGrammar.hs
	happy StqlGrammar.y
	happy StqlGrammar.y --info
	@chmod 755 StqlGrammar.hs

# Generate ML files from a lexer definition file
StqlTokens.hs : StqlTokens.x
	@rm -f StqlTokens.hs
	alex StqlTokens.x
	@chmod -w StqlTokens.hs

# Clean up the directory
clean::
	rm -rf Stql StqlTokens.hs StqlGrammar.hs *.hi *.o *.info


