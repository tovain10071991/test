# export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/user/Documents/llvm-3.4-build/lib/
CC=/home/user/Documents/llvm-3.4-build/bin/clang
CXX=/home/user/Documents/llvm-3.4-build/bin/clang++
LLVM_CONFIG?=/home/user/Documents/llvm-3.4-build/bin/llvm-config
VERBOSE := 1
ifndef VERBOSE
QUIET:=@
endif

SRC_DIR?=$(PWD)
LDFLAGS+=$(shell $(LLVM_CONFIG) --ldflags)
COMMON_FLAGS= -std=c++11
CXXFLAGS+=$(COMMON_FLAGS) $(shell $(LLVM_CONFIG) --cxxflags)
CPPFLAGS+=$(shell $(LLVM_CONFIG) --cppflags) -I$(SRC_DIR)

LLVMLIBS_LIBS=$(shell $(LLVM_CONFIG) --libs support core bitreader x86 jit interpreter)

PROJECT=myproject
PROJECT_OBJECTS=project.o

default: $(PROJECT)

%.o : $(SRC_DIR)/%.cpp
	@echo Compiling $*.cpp
	$(QUIET)$(CXX) -c $(CPPFLAGS) $(CXXFLAGS) $<

$(PROJECT) : $(PROJECT_OBJECTS)
	@echo Linking $@
	$(QUIET)$(CXX) -o $@ $(CXXFLAGS) $(LDFLAGS) $^ $(LLVMLIBS_LIBS)

clean::
	$(QUIET)rm -f $(PROJECT) $(PROJECT_OBJECTS)
