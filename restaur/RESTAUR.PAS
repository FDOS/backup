Program restaur;
{ More versatile replacement for DOS RESTORE.                                }
{ Handles backups made by DOS versions 2.0..4.01                             }
{ Free Software by TapirSoft Gisbert W.Selke, 24/03/91                       }
{$A+,B-,D+,E+,F-,I-,L+,N-,O-,R-,S-,V- }
{$M 16384,0,75000 }

  Uses DOS;

  Const progname  = 'RESTAUR';
        version   = '0.9';
        copyright = 'Free Software by TapirSoft Gisbert W.Selke, Mar 1991';
        bufsize   = 65000;
        CtrlC     = #3;
        CR        = #13;
        Esc       = #27;

  Type  namestring = string[80];

       fileheader32 = Record
                        lastone  : byte;
                        partno   : word;
                        dummy1   : word;
                        origname : Array [1..77] Of char;
                        orignamelength : byte;
                        dummy2   : Array [1..45] Of byte;
                      End;

       controlheader33 = Record
                           headerlen  : byte;
                           backupname : Array [1..8] Of char;
                           diskno     : word;
                           dummy      : Array [1..128] Of byte;
                         End;

       direntry = Record
                    dirname  : Array [1..63] Of char;
                    nentries : word;
                    dummy    : Array [1..4] Of byte;
                  End;

       fileentry = Record
                     filename : Array [1..12] Of char;
                     dummy1 : byte;
                     origlen : longint;
                     partno : word;
                     fileoffset : longint;
                     entrylen : longint;
                     attr : byte;
                     dummy2 : byte;
                     datetime : longint;
                   End;

       fileinfo = Record
                    oridir, dir, name : namestring;
                    orilen, offset, oridate : longint;
                    partnumber : word;
                    attrib : byte;
                   End;

       countryinfo = Record { really, only MSDOS 2.x+, PCDOS 3.0+ }
                       datefmt     : word;
                       currencystr : Array [1..5] Of char;
                       thousandsep : char;
                       fill1       : byte;
                       decimal     : char;
                       fill2       : byte;
                       datesep     : char;
                       fill3       : byte;
                       timesep     : char;
                       fill4       : byte;
                       currencyfmt : byte;
                       currencydig : byte;
                       timefmt     : byte;
                       casemapptr  : Pointer;
                       datalistsep : char;
                       fill5       : byte;
                       fill6       : Array [1..10] Of byte;
                     End;

       iobuffer = Array [1..bufsize] Of byte;

  Var backupfile, controlfile, destfile : File;
      backupname, controlname, myname, backupid, curorigdir : namestring;
      source, destination : namestring;
      bufptr : ^iobuffer;
      ctrlhead33 : controlheader33;
      dir33 : direntry;
      fil33 : fileentry;
      fil32 : fileheader32;
      countryinf : countryinfo;
      searchr32 : SearchRec;
      exitsave : Pointer;
      disknumber, nfiles, foundct : word;
      backupversion : byte;
      all, overwrite, origdir, firstone, quit, isopenbackup,
      isopencontrol, isopendest : boolean;

  {$F+ } Procedure myexit; {$F- }
  { catch all programme exits                                                }
  Begin                                                             { myexit }
    ExitProc := exitsave;
    If isopencontrol Then Close(controlfile);
    If isopenbackup Then Close(backupfile);
    If isopendest Then Close(destfile);
  End;                                                              { myexit }

  Function UpCase(ch:char):char;
  { adapted from Arne Sch„pers, TurboPascal 4.0 - Tips und Tricks            }
    Inline($58/$3C/$61/$72/$39/$3C/$7A/$76/$33/$3C/$84/$75/$02/$B0/$8E
    /$3C/$94/$75/$02/$B0/$99/$3C/$81/$75/$02/$B0/$9A
    /$3C/$87/$75/$02/$B0/$80/$3C/$86/$75/$02/$B0/$8F
    /$3C/$82/$75/$02/$B0/$90/$3C/$91/$75/$02/$B0/$92
    /$3C/$A4/$75/$02/$B0/$A5/$EB/03/90/$2C/$20);

  Function readkey : char;
  { emulate CRT ReadKey                                                      }
    Var regs : registers;
  Begin                                                            { ReadKey }
    With regs Do
    Begin
      ah := $07;
      Intr($21,regs);
      ReadKey := char(al);
    End;
  End;                                                             { ReadKey }

  Procedure clearline;
  { wipe clear current line                                                  }
  Begin                                                          { clearline }
    write(CR,' ':79,CR);
  End;                                                           { clearline }

  Procedure usage(err : byte);
  { show help and die                                                        }
  Begin                                                              { usage }
    If IOResult <> 0 Then;
    writeln;
    writeln('Restores DOS backups selectively, both DOS pre-3.3 and after');
    writeln;
    writeln('Usage:  ',myname,'  <sourcedrive> <destinationpath> [<options>]');
    writeln('  If <destinationpath> is just a drive,');
    writeln('  the original directory structure is preserved.');
    writeln('  Options are: /a : all files, no questions; /o : overwrite ',
            'existing files.');
    Halt(err);
  End;                                                               { usage }

  Procedure error(s : string; err : byte; showusage : boolean);
  { show error message, maybe usage hints, then die                          }
  Begin                                                              { error }
    If IOResult <> 0 Then;
    writeln;
    writeln(progname,' ',version,': ',s);
    If showusage Then usage(err);
    Halt(err);
  End;                                                               { error }

  Procedure getcountryinfo;
  { glean date/time format info from DOS                                     }
    Var regs : Registers;
  Begin                                                     { getcountryinfo }
    With regs Do
    Begin
      With countryinf Do
      Begin
        datesep := #0;
        timesep := #0;
        timefmt := 0;
        ax := $3800;
        ds := Seg(countryinf);
        dx := Ofs(countryinf);
        Intr($21,regs);
        If (flags And FCarry) <> 0 Then datefmt := 1;
        If datefmt > 2 Then datefmt := 1;
        If datesep < ' ' Then datesep := '/';
        If timesep < ' ' Then timesep := ':';
        If timefmt > 1 Then timefmt := 1;
      End;
    End;
  End;                                                      { getcountryinfo }

  Function intstr(w : word; digs : byte) : string;
  { turns number into a astring, given exact number of digits                }
    Var temp : string;
  Begin                                                             { intstr }
    Str(w,temp);
    While Length(temp) < digs Do temp := '0' + temp;
    Delete(temp,Succ(digs),255);
    intstr := temp;
  End;                                                              { intstr }

  Procedure opencontrolfile(Var success : boolean);
  { open files containing general info                                       }

    Var sr : SearchRec;
        bytesread : word;
        savefm, i : byte;

  Begin                                                    { opencontrolfile }
    savefm := FileMode;
    FileMode := 0;
    success := False;
    curorigdir := '';
    If backupversion = $33 Then
    Begin
      If isopenbackup Then Close(backupfile);
      If isopencontrol Then Close(controlfile);
      isopenbackup  := False;
      isopencontrol := False;
      FindFirst(source+'\CONTROL.*',AnyFile-Directory-VolumeID,sr);
      If DOSError = 0 Then
      Begin
        Assign(controlfile,source+'\'+sr.name);
        Reset(controlfile,1);
        If IOResult <> 0 Then error('Error opening backup file',4,False);
        isopencontrol := True;
        BlockRead(controlfile,ctrlhead33,SizeOf(ctrlhead33),bytesread);
        If SizeOf(ctrlhead33) <> bytesread Then error(
                                     'Invalid control file format',4,False);
        With ctrlhead33 Do
        Begin
          i := 1;
          backupid := '';
          While (i<=SizeOf(backupname)) And (backupname[i] >= ' ') Do
          Begin
            backupid := backupid + backupname[i];
            Inc(i);
          End;
          disknumber := diskno;
        End;
        success := True;
      End;
    End
    Else
    Begin
      firstone := True;
      success := True;
    End;
    FileMode := savefm;
  End;                                                     { opencontrolfile }

  Procedure getnextname(Var filinf1 : fileinfo; Var foundone : boolean);
  { get name of file to be restored next                                     }
    Var len, i : byte;
        bytesread : word;
  Begin                                                        { getnextname }
    If backupversion = $33 Then
    Begin
      foundone := False;
      Repeat
        BlockRead(controlfile,len,1,bytesread);
        If bytesread = 0 Then Exit;
        If bytesread <> 1 Then error('Invalid control file format',4,False);
        Case len Of
          34 : Begin { file entry proper }
                 BlockRead(controlfile,fil33,SizeOf(fil33),bytesread);
                 If bytesread <> SizeOf(fil33) Then
                               error('Invalid control file format',4,False);
                 foundone := True;
                 With fil33 Do
                 Begin
                   With filinf1 Do
                   Begin
                     dir := curorigdir;
                     oridir := curorigdir;
                     name := '';
                     i := 1;
                     While (i <= Length(filename)) And (filename[i] >= ' ') Do
                     Begin
                       name := name + filename[i];
                       Inc(i);
                     End;
                     orilen := origlen;
                     partnumber := partno;
                     offset := fileoffset;
                     attrib := attr;
                     oridate := datetime;
                   End;
                 End;
               End;
          70 : Begin { directory entry }
                 BlockRead(controlfile,dir33,SizeOf(dir33),bytesread);
                 If bytesread <> SizeOf(dir33) Then
                                 error('Invalid control file format',4,False);
                 i := 1;
                 curorigdir := '';
                 With dir33 Do
                 Begin
                   While (i <= Length(dirname)) And (dirname[i] >= ' ') Do
                   Begin
                     curorigdir := curorigdir + dirname[i];
                     Inc(i);
                   End;
                   nfiles := nentries;
                 End;
               End;
        End;
      Until foundone;
    End
    Else
    Begin
      Repeat
        If firstone Then FindFirst(source+'\*.*',
                                   AnyFile-Directory-VolumeId,searchr32)
                    Else FindNext(searchr32);
        firstone := False;
      Until searchr32.name <> 'BACKUPID.@@@';
      If DOSError = 0 Then
      Begin
        foundone := True;
        i := FileMode;
        FileMode := 0;
        Assign(backupfile,source+'\'+searchr32.name);
        Reset(backupfile,1);
        FileMode := i;
        BlockRead(backupfile,fil32,SizeOf(fil32),bytesread);
        If bytesread <> SizeOf(fil32) Then error('Invalid DOS 3.2 backup file',
                                                 3,False);
        With fil32 Do
        Begin
          With filinf1 Do
          Begin
            oridate := searchr32.time;
            partnumber := partno;
            If lastone = 0 Then orilen := -1
                           Else orilen := -2;
            attrib := 0;
            dir := '';
            name := '';
            i := 1;
            While (i <= SizeOf(origname)) And (origname[i] >= ' ') Do
            Begin
              If origname[i] In ['\','/'] Then
              Begin
                If dir <> '' Then dir := dir + '\';
                dir := dir + name;
                name := '';
              End
                Else name := name + origname[i];
              Inc(i);
            End;
            oridir := dir;
          End;
        End;
      End
        Else foundone := False;
    End;
    If foundone Then
    Begin
      With filinf1 Do
      Begin
        If (dir <> '') And (dir[Length(dir)] <> '\') Then dir := dir + '\';
        If (oridir <> '') And (oridir[Length(oridir)] <> '\') Then
                                                    oridir := oridir + '\';
        If origdir Then dir := destination+dir
                   Else dir := destination;
      End;
    End;
  End;                                                         { getnextname }

  Procedure restoreone(filinf1 : fileinfo);
  { restore a single file                                                    }

    Var ch : char;

    Procedure offerfile(filinf2 : fileinfo);
    { offer file for restoration                                             }

      Var dt : DateTime;

      Procedure showtime(dt : DateTime);
      { show date and time on OUTPUT                                         }
      Begin                                                       { showtime }
        With dt Do
        Begin
          With countryinf Do
          Begin
            Case datefmt Of
              0  : write(intstr(month,2),datesep,intstr(day,2),datesep,
                         intstr(year Mod 100,2));
              2  : write(intstr(year Mod 100,2),datesep,intstr(month,2),datesep,
                         intstr(day,2));
              Else write(intstr(day,2),datesep,intstr(month,2),datesep,
                         intstr(year Mod 100,2));
            End;
            write(' ');
            If timefmt = 0 Then
            Begin
              If hour <= 12 Then write(intstr(hour,2),timesep,
                                       intstr(min,2),'a.m.')
                            Else write(intstr(hour-12,2),timesep,
                                       intstr(min,2),'p.m.');
            End
              Else write(intstr(hour,2),timesep,intstr(min,2));
          End;
        End;
      End;                                                        { showtime }

    Begin                                                        { offerfile }
      With filinf2 Do
      Begin
        write('Restore ',oridir+name,', ');
        If orilen >= 0 Then write('size ',orilen,', ');
        UnpackTime(oridate,dt);
      End;
      showtime(dt);
      writeln(', to ',filinf2.dir);
      write('Copy/Rename/Destination/Skip/Quit/All? ');
      Repeat
        If all Then ch := 'A'
               Else ch := UpCase(ReadKey);
      Until ch In ['C','Y','1','D','R','S','Q',Esc,CtrlC,'A'];
      If ch In [Esc,CtrlC] Then ch := 'Q';
      writeln(ch);
      Case ch Of
        'K', 'Y', '1' : ch := 'C';
        'N', '0' : ch := 'S';
        Else ;
      End;
    End;                                                         { offerfile }

    Procedure rename(Var filinf2 : fileinfo);
    { offer file for renaming                                                }
      Var newname : namestring;
    Begin                                                           { rename }
      clearline;
      write('Old name: ',filinf2.name,'; new name (ENTER to keep): ');
      readln(newname);
      If newname <> '' Then filinf2.name := newname;
    End;                                                            { rename }

    Procedure changedest(Var filinf2 : fileinfo);
    { change file destination                                                }
      Var newdest : namestring;
    Begin                                                       { changedest }
      clearline;
      write('Destination: ',filinf2.dir,'; new destination (ENTER to keep): ');
      readln(newdest);
      If newdest <> '' Then
      Begin
        If newdest[Length(newdest)] <> '\' Then newdest := newdest + '\';
        filinf2.dir := newdest;
      End;
    End;                                                        { changedest }

    Procedure makedirs(dirs : namestring);
    { make directories as specified by dirs, if necessary and possible       }
      Var dir1, savedir, absdir, temp : namestring;
          l : byte;
    Begin                                                         { makedirs }
      absdir := '';
      GetDir(0,savedir);
      If dirs[Length(dirs)] <> '\' Then dirs := dirs + '\';
      While dirs <> '' Do
      Begin
        l := Pos('\',dirs);
        dir1 := Copy(dirs,1,Pred(l));
        Delete(dirs,1,l);
        absdir := absdir + dir1 + '\';
        If (Length(dir1) = 2) And (dir1[2] = ':') Then dir1 := dir1 + '\';
        ChDir(dir1);
        If IOResult <> 0 Then
        Begin
          MkDir(dir1);
          If IOResult <> 0 Then
          Begin
            ChDir(savedir);
            error('Cannot create '+absdir,6,False);
          End;
          ChDir(dir1);
        End;
      End;
      ChDir(savedir);
    End;                                                          { makedirs }

    Procedure checkexistfile(Var filinf2 : fileinfo);
    { check existence of file; if necessary, offer skip/rename/destination   }
      Var sr : SearchRec;
    Begin                                                   { checkexistfile }
      With filinf2 Do
      Begin
        FindFirst(dir+name,AnyFile,sr);
        If DOSError = 0 Then
        Begin
          clearline;
          writeln('File ',dir+name,' already exists.');
          write('Overwrite/Rename/Destination/Skip? ');
          If overwrite Then ch := 'O'
          Else
          Begin
            Repeat
              ch := UpCase(ReadKey);
              If ch In [Esc,CtrlC] Then ch := 'S';
            Until ch In ['O','R','D','S'];
          End;
          write(ch);
          If ch = 'O' Then ch := 'C';
        End
          Else ch := 'C';
      End;
    End;                                                    { checkexistfile }

    Procedure restorefile(filinf2 : fileinfo);
    { do the restoration                                                     }

      Var sr : SearchRec;
          done : longint;
          toread, bytesread : word;
          i : byte;

      Procedure opensourcefile;
      { open and position the file containing the backup data                }
      Begin                                                 { opensourcefile }
        If backupversion = $33 Then
        Begin
          If Not isopenbackup Then
          Begin
            FindFirst(source+'\BACKUP*.*',AnyFile-Directory-VolumeId,sr);
            If DOSError <> 0 Then error('Backup file missing from diskette',
                                        7,False);
            i := FileMode;
            FileMode := 0;
            Assign(backupfile,source+sr.name);
            Reset(backupfile,1);
            If IOResult <> 0 Then error('Cannot open backup file',7,False);
            FileMode := i;
            isopenbackup := True;
          End;
          Seek(backupfile,filinf2.offset);
        End
        Else
        Begin
          Seek(backupfile,SizeOf(fileheader32));
        End;
      End;                                                  { opensourcefile }

      Procedure getnewsourcedisk;
      { backup fil stretches disks; get next disk                            }
        Var filinf3 : fileinfo;
            ch : char;
            success, foundname : boolean;
      Begin                                               { getnewsourcedisk }
        If backupversion = $33 Then Close(controlfile);
        Close(backupfile);
        isopenbackup := False;
        isopencontrol := False;
        Repeat
          Repeat
            write(CR,'Please insert next disk for part ',
                  Succ(filinf2.partnumber),', then hit space bar: ');
            ch := UpCase(ReadKey);
            If ch In [CtrlC, Esc, 'Q'] Then error(
                                   'Restoration terminated by user',9,False);
            clearline;
            opencontrolfile(success);
          Until success;
          Repeat
            getnextname(filinf3,foundname);
            success := False;
            If foundname Then
            Begin
              If (filinf2.name   = filinf3.name) And
                 (filinf2.oridir = filinf3.oridir) Then
              Begin
                If Succ(filinf2.partnumber) = filinf3.partnumber Then
                                                               success := True
                Else
                Begin
                  writeln(CR,'Looking for part #',Succ(filinf2.partnumber),
                          ' but found part #',filinf3.partnumber);
                End;
              End;
            End;
          Until success Or Not foundname;
        Until success And foundname;
        filinf2 := filinf3;
        opensourcefile;
      End;                                                { getnewsourcedisk }

      Procedure opendestfile;
      { opens the file to be restored                                        }
      Begin                                                   { opendestfile }
        With filinf2 Do
        Begin
          Assign(destfile,dir+name);
          Rewrite(destfile,1);
          If IOResult <> 0 Then error('Cannot open output file '+
                               dir+name+' for output',8,False);
        End;
        isopendest := True;
      End;                                                    { opendestfile }

    Begin                                                      { restorefile }
      clearline;
      opensourcefile;
      opendestfile;
      done := 0;
      With filinf2 Do
      Begin
        While (done < orilen) Or (orilen < 0) Do
        Begin
          toread := bufsize;
          If (orilen >= 0) And (toread > orilen-done) Then
                                                       toread := orilen - done;
          Repeat
            BlockRead(backupfile,bufptr^,toread,bytesread);
            If bytesread = 0 Then
            Begin
              If orilen = -2 Then orilen := done
                             Else getnewsourcedisk;
            End;
          Until (bytesread <> 0) Or (orilen <= done);
          BlockWrite(destfile,bufptr^,bytesread,toread);
          If IOResult <> 0 Then error('Error writing output file',9,False);
          done := done + bytesread;
          If orilen > 0 Then write(CR,done/orilen*100:3:0,'%')
                        Else write(CR,(done+1023) ShR 10,'KB');
        End;
      End;
      clearline;
      SetFTime(destfile,filinf2.oridate);
      Close(destfile);
      isopendest := False;
      Close(backupfile);
      isopenbackup := False;
    End;                                                       { restorefile }

  Begin                                                         { restoreone }
    Inc(foundct);
    offerfile(filinf1);
    If ch = 'Q' Then
    Begin
      quit := True;
      Exit;
    End;
    If ch = 'A' Then all := True;
    Repeat
      If ch = 'S' Then Exit;
      If ch = 'R' Then rename(filinf1);
      If ch = 'D' Then changedest(filinf1);
      If (filinf1.dir <> '') And ((Length(filinf1.dir) <> 2) Or
         (filinf1.dir[2] <> ':')) Then makedirs(filinf1.dir);
      checkexistfile(filinf1);
    Until ch In ['C', 'S'];
    If ch = 'C' Then restorefile(filinf1);
  End;                                                          { restoreone }

  Procedure dorestore;
  { offer files for restoration; maybe even do it                            }
    Var foundone : boolean;
        filinf : fileinfo;
  Begin                                                          { dorestore }
    isopencontrol := False;
    isopenbackup := False;
    opencontrolfile(foundone);
    If foundone Then getnextname(filinf,foundone);
    While foundone And (filinf.name <> '') And (Not quit) Do
    Begin
      If filinf.partnumber = 1 Then restoreone(filinf);
      getnextname(filinf,foundone);
    End;
    If isopencontrol Then Close(controlfile);
    isopencontrol := False;
    If foundct = 0 Then error('No backup files starting on this disk',10,False);
  End;                                                           { dorestore }

  Procedure checkversion;
  { finds out which DOS version the backup was made by                       }
    Var sr : SearchRec;
  Begin                                                       { checkversion }
    FindFirst(source+'BACKUPID.@*',AnyFile,sr);
    If DOSError = 0 Then backupversion := $32
    Else
    Begin
      FindFirst(source+'CONTROL.*',AnyFile,sr);
      If DOSError = 0 Then backupversion := $33
                      Else error('Disk in drive '+source+
                                 ' is not a valid DOS backup disk',3,False);
    End;
    write('Backup made by DOS ');
    If backupversion = $33 Then writeln('3.3 or later')
                           Else writeln('3.2 or earlier');
  End;                                                        { checkversion }

  Procedure getargs;
  { get arguments from command line                                          }
    Var i, k : byte;
        temp: string;
  Begin                                                            { getargs }
    isopencontrol := False;
    isopenbackup  := False;
    isopendest    := False;
    exitsave := ExitProc;
    ExitProc := @myexit;
    myname := ParamStr(0);
    If myname = '' Then myname := progname;
    source := '';
    destination := '';
    all := False;
    overwrite := False;
    For i := 1 To ParamCount Do
    Begin
      temp := ParamStr(i);
      For k := 1 To Length(temp) Do temp[k] := UpCase(temp[k]);
      If (Length(temp) = 2) And (temp[1] In ['/','-']) Then
      Begin
        Case temp[2] Of
          'A' : all := True;
          'O' : overwrite := True;
          'H', '?' : usage(1);
          Else error('Unknown command line switch',2,True);
        End
      End
      Else
      Begin
        If temp = '?' Then usage(1);
        If source = '' Then source := temp
        Else
        Begin
          If destination = '' Then destination := temp
                              Else error('Too many acommand line arguments',
                                         2,True);
        End;
      End;
    End;
    If destination = '' Then error('Command line arguments missing',2,True);
    If Length(source) = 1 Then source := source + ':';
    If Length(source) <> 2 Then error('Argument #1 must be plain source drive',
                                      2,True);
    If (Length(destination) = 1) And (destination <> '.') Then
                                          destination := destination + ':';
    origdir := Length(destination) = 2;
    If destination[Length(destination)] <> '\' Then
                                          destination := destination + '\';
    If MaxAvail >= SizeOf(iobuffer) Then New(bufptr);
    quit := False;
    foundct := 0;
    getcountryinfo;
  End;                                                             { getargs }

Begin                                                                 { main }
  writeln(progname,' ',version,' -- ',copyright);
  getargs;
  checkversion;
  dorestore;
End.
