import java.io.*;
import java.util.*;

public class BasicRegionGeneratorTest{
    static final String OUTPUT_FILE = "BasicRegionGeneratorTest.v";
    static final String[] IMPORTS = {"List", "Vector", "BasicRegion", "Boundary", "Region"};
    static final BasicRegionGenerator testBasicRegionGenerator = BasicRegionGenerator.makeBasicRegionGenerator(BoundaryGardenTest.testGarden, 0);
    static final String NAME = "testBasicRegionGenerator";

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/" + OUTPUT_FILE);
	for (String imp : IMPORTS)
	    writer.println(CoqObjectTest.REQUIRE_IMPORT + " " + imp + ".");
	writer.println("Import VectorNotations.");
	writer.println();
	writer.println(testBasicRegionGenerator.definition(NAME));
	writer.close();
    }
}
