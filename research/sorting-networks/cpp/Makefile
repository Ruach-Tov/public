CXX = g++
CXXFLAGS = -std=c++17 -O2 -Wall -Wextra

.PHONY: all test clean

all: test_robdd

test_robdd: test_robdd.cpp robdd.hpp
	$(CXX) $(CXXFLAGS) -o $@ test_robdd.cpp

test: test_robdd
	./test_robdd

clean:
	rm -f test_robdd
