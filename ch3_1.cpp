#include <iostream>
#include <cstring>
#include <cstdlib>


#include <time.h>

#include <CGAL/Point_3.h>
#include <CGAL/Exact_predicates_exact_constructions_kernel.h>
#include <CGAL/point_generators_3.h>
#include <CGAL/function_objects.h>
#include <CGAL/Polyhedron_3.h>

#include <CGAL/Polyhedron_incremental_builder_3.h>
#include <CGAL/Modifier_base.h>


#include <vector>
#include <set>

#define CUBE

//#define PERTURBATION




//typedef CGAL::Tag_true Supports_halfedge_prev;


typedef CGAL::Exact_predicates_exact_constructions_kernel Kernel;
typedef Kernel::Point_3 Point_3;
typedef CGAL::Creator_uniform_3<double,Point_3>  Creator;

typedef CGAL::Polyhedron_3<Kernel> Polyhedron;
typedef CGAL::Polyhedron_3<Kernel>::Vertex Vert;

typedef std::vector<Point_3> Points;
typedef std::vector<Point_3>::iterator pveciterator;

typedef Polyhedron::Vertex Vertex;
typedef Polyhedron::Facet Facet;

using namespace std;


int beaneath_beyond_3(vector<Point_3>::iterator start, vector<Point_3>::iterator fin,
	Polyhedron& P, bool some_bool);


set<Polyhedron::Facet_handle>* fvisited;
/* I use this set to ensure that a facet won't be visited twice
 * by the delete_redundant function. This function traverses the graph
 * of the facets. Deletes facets that need to be deleted
 */



/*incremental builder to add facets to the new point */

/* in order to have the info of the edges and the point 
 * which they are going to be connected, we store
 * globally a vector  of  point ,which represents the 2d convex hull
 * where the "hole" in our polytope exists */



/* in order to communicate with the builder without
 * using any arguments,  I am using these global pointers
 * to structures that are created in main 
 */

set <Polyhedron::Halfedge_handle>*  tbc_edges;	//border edges, to be connected to the new point , input structure
vector <Polyhedron::Facet_handle>*  inc_f;		//incident facets to the new point, output structure

Point_3 *newpoint;								//newest point
int total_points ;								//total number of points, used for IDing points

template <class HDS>
class NewP_Connector : public CGAL::Modifier_base<HDS> {
public:
    NewP_Connector() {}
    void operator()( HDS& hds) {
        // Postcondition: hds is a valid polyhedral surface.

    	/*Need to construct a valid map from Vertex -> Id
    	 * right now we have the inverse map Id -> vertex via
    	 * function Vertex_Handle vertex(size_t id)
    	 */

    	int size = tbc_edges->size();

    	map <Polyhedron::HalfedgeDS::Vertex_handle, size_t> vid;

    	




        CGAL::Polyhedron_incremental_builder_3<HDS> B( hds, true);


        B.begin_surface( 1, size, size, CGAL::Polyhedron_incremental_builder_3< HDS >::ABSOLUTE_INDEXING
);

        Polyhedron::Vertex_handle h;
        Polyhedron::Halfedge_handle hh;


        /* in order to Id all the previous vertices properly use this Vid map */
        for (int i=0; i < total_points; i++) {
        	h = B.vertex(i);
    		vid[h] = i;
        }
        typedef typename HDS::Vertex   Vertex;
        typedef typename Vertex::Point Point;

        typename HDS::Vertex_handle v;

        Point_3 newp = *newpoint;
        v = B.add_vertex(newp);
        Polyhedron::Facet_handle fh;

        int newpId = total_points; 

        /* for reach edge  to be connected */
        for (set<Polyhedron::Halfedge_handle>::iterator it=tbc_edges->begin(); it != 
        	tbc_edges->end(); it++) {

        	B.add_vertex((*it)->vertex()->point());

        	B.add_vertex((*it)->opposite()->vertex()->point());

        	/*create the appropriate facet */
       		fh = B.begin_facet();

       		B.add_vertex_to_facet(newpId);

       		//error prevention
       		if (vid.find(h) == vid.end()) {
       			exit(0);
       		}


       		int myid = vid[(*it)->vertex()];
       		
       		B.add_vertex_to_facet(myid);

       		myid = vid[(*it)->prev()->vertex()];
       		
       		B.add_vertex_to_facet(myid);

       		inc_f->push_back(fh);
       		B.end_facet();

    	}
    	B.end_surface();
    	B.remove_unconnected_vertices();
    }
};




/* recursive function for deleting fcaets */



int delete_redundant(Point_3 &newp , Polyhedron::Facet_handle facet, Point_3 &reference,
	set <Polyhedron::Facet_handle> &hah, Polyhedron::Halfedge_handle parent, Polyhedron &P)	
	//parent used to find the purple halfedges
{
	/*ensure that no facet is visited after it's deleted or after
	 * it has already been visited */
	if (fvisited->find(facet) != fvisited->end()) {
		return 0;
	}
	else
		fvisited->insert(facet);
	
	Point_3 ref = reference;

	/*find out the points of the vertex*/

	Polyhedron::Halfedge_around_facet_circulator circ = facet->facet_begin();

	Point_3 list[3];
	Polyhedron::Facet_handle facet_list[3];		/*find the incident facets, to call them after the deletion*/
	Polyhedron::Halfedge_handle he_list[3];
	int i = 0;
	int rflag = 0;		//if the reference point is included in a facet
	do {

		list[i] = circ->vertex()->point();
		if (list[i] == reference) 
			rflag = 1;
		i++;
		circ++;
	} while (circ != facet->facet_begin());
	/*if rflag == 1, means our facet contains the reference point*
	 * so find a new reference point */
	for (Polyhedron::Vertex_iterator it = P.vertices_begin(); it != P.vertices_end() && rflag == 1; it++) {

		if (it->point() != list[0] && it->point() != list[1] && it->point() != list[2]) {
			ref = it->point();
			break;
		}
	}

	/*check the orientation, == means that it is on the same side as the 1st point*/

	if (CGAL::coplanar(list[0], list[1], list[2], newp) || (
		CGAL::coplanar(list[0], list[1], list[2], ref)) ) {
		cerr << "DEGENERECY" << endl;
		exit(-1);
	}

	if ((CGAL::orientation(list[0], list[1], list[2], newp) != 
		CGAL::orientation(list[0], list[1], list[2], ref))) {

		/*first find the incident facets, then delete the facet*/

		circ = facet->facet_begin();
		i = 0;
		do {

			
			if (circ->opposite()->facet() != NULL) {

				he_list[i] = circ->opposite();
				facet_list[i++] = circ->opposite()->facet();
			}
			

			
			circ++;
		} while (circ != facet->facet_begin());
		P.erase_facet(circ);
		int n = i;

		for (i=0; i < n; i++)
			delete_redundant(newp, facet_list[i], reference, hah, he_list[i], P);
	}
	/*else we reached blue facets, we need to add the purple halfedges */
	else {

		hah.insert(facet);
		return 0;
	}


	return 1;

}


typedef Polyhedron::HalfedgeDS             HalfedgeDS;


int main(int argc, char *argv[])
{

	int npoints = 1024;

	if (argc > 2 && !strcmp(argv[1], "-n"))
		npoints = atoi(argv[2]);


	Points points;
	points.reserve(npoints);
#ifdef CUBE
	CGAL::Random_points_in_cube_3<Point_3, Creator> g( 1000.0);
#else
	CGAL::Random_points_in_sphere_3<Point_3, Creator> g( 1000.0);
#endif
	CGAL::cpp11::copy_n( g, npoints, std::back_inserter(points));

	Polyhedron P;

/*handle degeneracies by perturbation */
#ifdef PERTURBATION


	/*handle degenarcies by moving the points by 10^(-9) to 10^(-6)*/
	for (int i=0; i < points.size(); i++) {

		points[i].x() += ((double) (rand()%1000 - 500))/100000000.0;
		points[i].y() += ((double) (rand()%1000 - 500))/100000000.0;
		points[i].z() += ((double) (rand()%1000 - 500))/100000000.0;
	}

#endif

	/* first sort the points according to X*/
	beaneath_beyond_3( points.begin(), points.end(), P, true);	//also prints, for easiness purposes
	return 0;

}

int beaneath_beyond_3(vector<Point_3>::iterator start, vector<Point_3>::iterator fin,
	Polyhedron& P, bool some_bool)
{	
	int sttime = clock();

	sort(start, fin);

	Point_3 pts[4];

	for (int i=0; i < 4 ; i++,start++) {
		pts[i] = *start;
	}

	


	P.make_tetrahedron(pts[0],pts[1], pts[2], pts[3]);
	

	Point_3 reference = pts[0];
	
	/* global data used for the incremental builder */

	vector <Polyhedron::Facet_handle> inc_vert;	//incidents vertices, used to start the removal
	set <Polyhedron::Facet_handle> hah;			//facets who contain border halfedge
	set <Polyhedron::Halfedge_handle> hfe;		//halfedges that are border 



	/* first determine which facets are incident to the last point */
	int k = 0;
	for (Polyhedron::Vertex_iterator it = P.vertices_begin();it != P.vertices_end(); it++) {

		if (it->point() == pts[3]) {

			/* for every halfedge arround the vertex*/
			Polyhedron::Halfedge_around_vertex_circulator circ = it->vertex_begin();
			
			/* add the incident facets to the structure*/
			do {

				inc_vert.push_back(circ->facet());

				
				circ++;
			} while (circ != it->vertex_begin());

			break;
		}
			
	}


	/*incremental builder */
	NewP_Connector<HalfedgeDS> cnc;

	for (int i=4; start != fin; start++, i++) {
		Point_3 newp = *start;

		/*the incidents facets to the last points are stored in inc_vert*/

		fvisited = new set<Polyhedron::Facet_handle>();


		for (int j=0; j < inc_vert.size(); j++)
			delete_redundant( newp, inc_vert[j], reference, hah, NULL, P);

		delete fvisited;
		
		/*now add connect the new point with all the edges that are left without a border*/

		/*global vars initialization*/
		hfe.clear();
		for (set<Polyhedron::Facet_handle>::iterator it=hah.begin(); it != 
        	hah.end(); it++) {
			Polyhedron::Facet_handle f = *it;
			Polyhedron::Halfedge_around_facet_circulator circ = f->facet_begin();
			
			do {
				if (circ->is_border_edge()) {
					hfe.insert(circ);
				}
				circ++;
			} while (circ != f->facet_begin());

		}
		
		tbc_edges = &hfe;
		newpoint = &newp;
		inc_vert.clear();
		inc_f = &inc_vert;
		/*count the vertices in P*/

		int c = 0;
		for (Polyhedron::Vertex_iterator it = P.vertices_begin();it != P.vertices_end(); it++) {
			c++;
		}
		
		total_points = c;

		
		P.delegate(cnc);
		
		hah.clear();

		
		
		
	}

	/*print out the result points */
	for (Polyhedron::Vertex_iterator it = P.vertices_begin();it != P.vertices_end(); it++)
		cout << it->point() << endl;

	double et = ((double) clock() - sttime)/CLOCKS_PER_SEC;

	cout << "\n\ntime = " <<et << endl;

}	

