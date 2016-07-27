import java.io.*;
import java.util.*;

public class BasicRegionGeneratorTest{

    static final String OUTPUT_FILE = "BasicRegionGeneratorTest.v";
    static final String[] IMPORTS = {"List", "BasicRegion", "Boundary", "Region"};
    static final String REQUIRE_IMPORT = "Require Import";

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/" + OUTPUT_FILE);
	for (String imp : IMPORTS)
	    writer.println(REQUIRE_IMPORT + " " + imp + ".");
	writer.println();
	Vertex a = new Vertex(0);
	Vertex b = new Vertex(1);
	Vertex c = new Vertex(2);
	Vertex[] topPath = {a, b, c};
	Vertex[] bottomPath = {a, c};
	Boundary testBoundary = new Boundary(new ArrayList<Vertex>(Arrays.asList(topPath)), 
					     new ArrayList<Vertex>(Arrays.asList(bottomPath)));
	Boundary[] boundaries = { testBoundary };
	BoundaryGarden myGarden = new BoundaryGarden(new ArrayList<Boundary>(Arrays.asList(boundaries)),
						     new ArrayList<String>(Arrays.asList("testBoundary")));
	BasicRegionGenerator testBasicRegionGenerator = new BasicRegionGenerator(myGarden, 0);
	writer.println(testBasicRegionGenerator.toCoq().definition("testBasicRegionGenerator"));
	writer.close();
    }
}
