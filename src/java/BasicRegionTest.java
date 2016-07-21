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
	Integer[] topPath = {0, 1, 2};
	Integer[] bottomPath = {0, 2};
	Boundary testBoundary = new Boundary(new ArrayList<Integer>(Arrays.asList(topPath)), 
					     new ArrayList<Integer>(Arrays.asList(bottomPath)),
					     "testBoundary");
	Boundary[] boundaries = { testBoundary };
	BoundaryGarden myGarden = new BoundaryGarden(new ArrayList<Boundary>(Arrays.asList(boundaries)),
						     new ArrayList<String>(Arrays.asList("testBoundary")),
						     "myGarden");
	BasicRegion testBasicRegion = new BasicRegion(myGarden, 0, 1, 2, true, false);
	writer.println(testBasicRegion.toCoq().definition("testBasicRegion"));
	writer.close();
    }
}
