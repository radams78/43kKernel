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
	BasicRegion testBasicRegion = new BasicRegion(BoundaryGardenTest.testGarden, 0, InternalType.isolated, InternalType.top, true, false);
	writer.println(testBasicRegion.toCoq().definition("testBasicRegion"));
	writer.close();
    }
}
