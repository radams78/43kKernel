import java.io.*;
import java.util.*;

public class BasicRegionGeneratorTest{
    static final String OUTPUT_FILE = "BasicRegionGeneratorTest.v";
    static final String[] IMPORTS = {"List", "BasicRegion", "Boundary", "Region"};
    static final BasicRegionGenerator testBasicRegionGenerator = BasicRegionGenerator.makeBasicRegionGenerator(BoundaryGardenTest.testGarden, 0);
    static final String NAME = "testBasicRegionGenerator";

    public static void main(String[] args) throws FileNotFoundException {
	CoqObjectTest.testObject(args[0], OUTPUT_FILE, IMPORTS, testBasicRegionGenerator, NAME);
    }
}
