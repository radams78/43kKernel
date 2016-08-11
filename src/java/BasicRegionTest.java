import java.io.*;
import java.util.*;

public class BasicRegionTest{
    static final String OUTPUT_FILE = "BasicRegionTest.v";
    static final String[] IMPORTS = {"BasicRegion", "Boundary", "Region", "Vector"}; 
    static final BasicRegion testBasicRegion = new BasicRegion(BoundaryGardenTest.testGarden, 0, InternalType.isolated, InternalType.top, true, false);
    static final String NAME = "testBasicRegion";

    //TODO Duplication
    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/" + OUTPUT_FILE);
	for (String imp : IMPORTS)
	    writer.println(CoqObjectTest.REQUIRE_IMPORT + " " + imp + ".");
	writer.println("Import VectorNotations.");
	writer.println();
	writer.println(testBasicRegion.definition(NAME));
	writer.close();
    }
}
