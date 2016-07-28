all: bin doc src/coq/BoundaryTest.vo src/coq/BasicRegionTest.vo src/coq/BasicRegionGeneratorTest.vo
bin: $(shell ls src/java/*.java)
	javac -d bin src/java/*.java
doc:
	javadoc -d doc src/java/*.java
test: src/coq/BoundaryTest.vo src/coq/BasicRegionTest.vo src/coq/BasicRegionGeneratorTest.vo testVertex
testVertex: bin
	@cd bin; java -ea VertexTest
src/coq/%.vo: bin
	@cd bin; java -ea $* ../src/coq
	@cd src/coq; coqc $*
