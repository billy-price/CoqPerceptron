CC = g++
CFLAGS = -std=c++11

SRC = \
	perceptron.cpp \
	data_generator.cpp \
	makeplotfiles.cpp
BIN = $(SRC:.cpp=)

COMPILE = $(CC) $(CFLAGS) $< -o $@

ifeq ($(OPTIMIZE), 1)
	CFLAGS += -O2
endif

all: $(BIN)

perceptron: perceptron.cpp
	$(COMPILE) -lgmp

data_generator: data_generator.cpp
	$(COMPILE)

makeplotfiles: makeplotfiles.cpp
	$(COMPILE)

clean:
	rm -f $(BIN)

.PHONY: all clean
