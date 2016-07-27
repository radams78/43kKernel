import java.io.*;
import java.util.*;

public class BasicRegionTest{

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/BasicRegionTest.v");
	writer.println("Require Import List.");
	writer.println("Require Import BasicRegion.");
	writer.println("Require Import Boundary.");
	writer.println("Require Import Region.");
	writer.println();
	Vertex a = new Vertex(0);
	Vertex b = new Vertex(1);
	Vertex c = new Vertex(2); // TODO Duplication with BasicRegionGeneratorTest
	Vertex[] topPath = {a, b, c};
	Vertex[] bottomPath = {a, c};
	Boundary testBoundary = new Boundary(new ArrayList<Vertex>(Arrays.asList(topPath)), 
					     new ArrayList<Vertex>(Arrays.asList(bottomPath)));
	Boundary[] boundaries = { testBoundary };
	BoundaryGarden myGarden = new BoundaryGarden(new ArrayList<Boundary>(Arrays.asList(boundaries)),
						     new ArrayList<String>(Arrays.asList("testBoundary")));
	BasicRegion testBasicRegion = new BasicRegion(myGarden, 0, InternalType.isolated, InternalType.top, true, false);
	writer.println(testBasicRegion.toCoq().definition("testBasicRegion"));
	writer.close();
    }
}
