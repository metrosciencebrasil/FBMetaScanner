{******************************************************************************
  FBMetaScanner - Delphi 12 / VCL / FireDAC / Firebird 5

  Componente visual que procura possiveis causas do erro:
    [FireDAC][Phys][FB] Dynamic SQL Error. SQL error code = -817
    Metadata update statement is not allowed by the current database SQL dialect 3
  e, de forma geral, problemas de migracao Firebird 2.5 -> Firebird 5.0:
    - palavras reservadas novas (FB3/FB4) usadas como identificadores
    - UDFs (ib_udf/fbudf/FreeUDFLib) desabilitadas no FB4+
    - CURRENT_TIMESTAMP/TIME WITH TIME ZONE e INT128 (campos persistentes)
    - triggers AFTER alterando NEW, OLD somente leitura, RDB$ somente leitura
    - RDB$USERS removida, SET GENERATOR, WHEN SQLCODE, PLAN fixo
    - fbclient antiga/fbembed, Srp x Legacy_Auth, WNET removido, charset NONE
    - parametro SQLDialect (FireDAC ignora "Dialect"), driver IB, IBX
    - (banco conectado) ODS, UDFs declaradas, tabelas externas, objetos com
      nomes reservados e codigo-fonte de procedures/triggers/views

  Modos de varredura:
    1) Form      - inspeciona os componentes VIVOS do form (e DataModules abertos)
    2) Unit      - le uma .pas (e a .dfm correspondente) escolhida pelo usuario
    3) Projeto   - le recursivamente todas as .pas / .dfm / .dpr / .sql
                   (e FDConnectionDefs.ini)
    4) Banco     - conecta (se preciso) e analisa os metadados do banco

  Uso rapido (em tempo de execucao, sem instalar pacote):
    uses FBMetaScanner;
    with TFBMetaScanner.Create(Self) do
    begin
      Parent := Self;
      Align  := alClient;
    end;

  Para instalar na paleta: adicione esta unit a um pacote de design-time
  (requires: rtl, vcl, FireDAC, FireDACCommonDriver, FireDACCommon,
   FireDACPhysFBDriver, designide) e instale. Aparece na aba "Diagnostico".
******************************************************************************}
unit FBMetaScanner;

interface

uses
  System.SysUtils, System.Classes, System.StrUtils, System.IOUtils,
  System.RegularExpressions, System.Generics.Collections,
  System.Generics.Defaults, System.Variants,
  Winapi.Windows,
  Vcl.Controls, Vcl.Forms, Vcl.StdCtrls, Vcl.ExtCtrls, Vcl.ComCtrls,
  Vcl.Dialogs, Vcl.Clipbrd, Vcl.Graphics,
  Data.DB,
  FireDAC.Stan.Intf, FireDAC.Stan.Option,
  FireDAC.Phys.FB, FireDAC.Comp.Client, FireDAC.Comp.Script;

type
  TFBSeverity = (fsError, fsWarning, fsInfo);

  /// tmRaw = SQL puro (componentes, .sql, fontes do banco)
  /// tmQuoted = so o conteudo de literais '...' (.pas / .dfm)
  TFBTextMode = (tmRaw, tmQuoted);

  TFBFinding = record
    Severity: TFBSeverity;
    Source: string;
    Line: Integer;
    Msg: string;
    Fix: string;
  end;

  TFBMetaScanner = class(TCustomPanel)
  private
    FConnection: TFDConnection;
    FTargetForm: TCustomForm;
    FProjectDir: string;
    FIncludeDataModules: Boolean;
    FFindings: TList<TFBFinding>;
    FSeen: TList<TComponent>;
    FReported: TDictionary<string, Boolean>;
    FCurSource: string;
    FRootDir: string;
    FFoundFBConn: Boolean;
    FFoundLink: Boolean;
    // UI
    FTop: TPanel;
    FBtnForm, FBtnUnit, FBtnProject, FBtnDB, FBtnCopy, FBtnClear: TButton;
    FStatus: TLabel;
    FList: TListView;
    FDetail: TMemo;

    procedure SetConnection(const Value: TFDConnection);
    procedure SetTargetForm(const Value: TCustomForm);
    function MakeButton(const ACaption: string; ALeft, AWidth: Integer;
      AHandler: TNotifyEvent): TButton;
    procedure BtnFormClick(Sender: TObject);
    procedure BtnUnitClick(Sender: TObject);
    procedure BtnProjectClick(Sender: TObject);
    procedure BtnDBClick(Sender: TObject);
    procedure BtnCopyClick(Sender: TObject);
    procedure BtnClearClick(Sender: TObject);
    procedure ListSelectItem(Sender: TObject; Item: TListItem; Selected: Boolean);
    procedure ListCustomDrawItem(Sender: TCustomListView; Item: TListItem;
      State: TCustomDrawState; var DefaultDraw: Boolean);

    procedure BeginScan;
    procedure EndScan;
    procedure RefreshList;
    procedure SetBusy(ABusy: Boolean; const AText: string = '');
    procedure AddFinding(ASev: TFBSeverity; const ASource: string; ALine: Integer;
      const AMsg, AFix: string);
    function Once(const AKey: string): Boolean;

    // varredura viva
    procedure ScanComponents(AOwner: TComponent; const APath: string);
    procedure CheckComponent(C: TComponent; const AWhere: string);
    procedure CheckConnection(AConn: TFDConnection; const AWhere: string);
    procedure CheckFBParams(AParams: TStrings; const ADriver, AWhere: string;
      ALine: Integer);
    procedure CheckLiveDatabase(AConn: TFDConnection; const AWhere: string);
    procedure CheckLiveMigration(AConn: TFDConnection; const AWhere: string);
    procedure ScanDbSources(AConn: TFDConnection; const AWhere: string);
    procedure CheckTransaction(ATx: TFDTransaction; const AWhere: string);
    procedure CheckDriverLink(ALink: TFDPhysFBDriverLink; const AWhere: string);
    procedure CheckLoadedClient;
    procedure CheckClientLib(const APath, AWhere: string; ALine: Integer);
    procedure ReportIBX(const ACls, AWhere: string; ALine: Integer);
    procedure ReportReadConsistency(const AWhere: string; ALine: Integer);
    function ResolveLib(const APath: string): string;
    function FindFirstConnection: TFDConnection;

    // varredura de arquivos
    procedure ScanFile(const AFile: string);
    procedure ScanPas(ALines: TStrings);
    procedure ScanDfm(ALines: TStrings);
    procedure ScanIni(ALines: TStrings);
    procedure ScanSqlFile(ALines: TStrings);
    procedure AnalyzeDfmBlock(const ACls, AName: string; ABlock: TStrings;
      AStartLine: Integer);
    function ScanSQLLines(ALines: TStrings; const AWhere: string;
      ABaseLine: Integer; AComponentMode, AMultiOK: Boolean): Integer;
    procedure ScanMigration(ALines: TStrings; const AWhere: string;
      ABaseLine: Integer; AMode: TFBTextMode; ATrigCtx: Integer);
    procedure CheckPersistentSQL(const ASQL, AWhere: string; ALine: Integer);
    function RelName(const AFile: string): string;
  protected
    procedure Notification(AComponent: TComponent; Operation: TOperation); override;
  public
    constructor Create(AOwner: TComponent); override;
    destructor Destroy; override;

    procedure ScanForm;
    procedure ScanUnit(const AFileName: string = '');
    procedure ScanProject(const ADir: string = '');
    procedure ScanDatabase(AConn: TFDConnection = nil);
    procedure Clear;
    function ReportText: string;
    function ErrorCount: Integer;
  published
    /// Conexao a inspecionar alem das encontradas no form (opcional)
    property Connection: TFDConnection read FConnection write SetConnection;
    /// Form a varrer; se vazio usa o form onde o componente esta
    property TargetForm: TCustomForm read FTargetForm write SetTargetForm;
    /// Pasta do projeto; se vazio o botao Projeto pergunta
    property ProjectDir: string read FProjectDir write FProjectDir;
    /// Inclui os TDataModule abertos na varredura do form
    property IncludeDataModules: Boolean read FIncludeDataModules
      write FIncludeDataModules default True;
    property Align;
    property Anchors;
    property Visible;
    property Enabled;
  end;

procedure Register;

implementation

const
  RX_DDL = '\b(CREATE|ALTER|DROP|RECREATE)\s+(OR\s+ALTER\s+)?(GLOBAL\s+TEMPORARY\s+)?' +
    '(TABLE|VIEW|PROCEDURE|TRIGGER|DOMAIN|INDEX|GENERATOR|SEQUENCE|EXCEPTION|' +
    'FUNCTION|PACKAGE|ROLE)\b';
  RX_SYSTAB = '\b(UPDATE|DELETE\s+FROM|INSERT\s+INTO)\s+RDB\$\w+';
  RX_SETDIALECT = '\bSET\s+SQL\s+DIALECT\b';
  RX_ALTERDB = '\bALTER\s+DATABASE\b';
  RX_DIALECT = 'Dialect[''"\]\s]*[:=]+\s*[''"]?(\d)';
  RX_DML = '\b(INSERT\s+INTO|DELETE\s+FROM)\b|(?<!\bON\s)\bUPDATE\s+\w';
  RX_COMMIT = '\bCommit(Retaining)?\b';
  RX_TYPES = '\b(BIGINT|DATE|TIME|TIMESTAMP|DECIMAL|NUMERIC)\b';

  // ---- migracao 2.5 -> 5.0 ----
  RX_UDF = '\b(STRLEN|SUBSTRLEN|SUBSTR|LTRIM|RTRIM|DIV|ADDDAY|ADDHOUR|ADDMINUTE|' +
    'ADDMONTH|ADDSECOND|ADDMILLISECOND|ADDWEEK|ADDYEAR|GETEXACTTIMESTAMP|I64ROUND|' +
    'I64TRUNCATE|I64NULLIF|I64NVL|INULLIF|INVL|DNULLIF|DNVL|SNULLIF|SNVL|DOW|SDOW|' +
    'STRING2BLOB|DPOWER|SRIGHT|TRUNCATE)\s*\(';
  RX_UDF3RD = '\b((?:F|RF|UDF)_[A-Z]\w*)\s*\(';
  RX_EXTFUNC = '\bDECLARE\s+EXTERNAL\s+FUNCTION\b';
  RX_CURTS = '\bCURRENT_TIME(STAMP)?\b';
  RX_SETGEN = '\bSET\s+GENERATOR\b';
  RX_RESTART = '\bRESTART\s+WITH\b';
  RX_SQLCODE = '\bWHEN\s+SQLCODE\b';
  RX_RDBUSERS = '\bRDB\$USERS\b';
  RX_SYSFLAG = '\bRDB\$SYSTEM_FLAG\s+IS\s+NULL\b';
  RX_DQSTR = '(=|<>|\bLIKE)\s*"[^"]+"';
  RX_TRGHDR = '\b(BEFORE|AFTER)\s+(INSERT|UPDATE|DELETE)\b';
  RX_NEWASSIGN = '(?:^|;|\bTHEN\b|\bELSE\b|\bBEGIN\b|\bDO\b)\s*NEW\.(\w+)\s*=(?!=)';
  RX_OLDASSIGN = '(?:^|;|\bTHEN\b|\bELSE\b|\bBEGIN\b|\bDO\b)\s*OLD\.(\w+)\s*=(?!=)';
  RX_PLAN = '\bPLAN\s*\(';
  RX_CSNONE = '\bCHARACTER\s+SET\s+NONE\b';
  RX_SETTERM = '\bSET\s+TERM\b';
  RX_AGG = '\b(SUM|AVG)\s*\(';
  RX_IBXCLS = '\b(TFDPhysIBDriverLink|TIBDatabase|TIBTransaction|TIBQuery|TIBSQL|' +
    'TIBDataSet|TIBTable|TIBStoredProc|TIBUpdateSQL)\b';

  // palavras reservadas novas (eram identificadores validos no 2.5)
  FB_RES30: array of string = ['BOOLEAN', 'CORR', 'COVAR_POP', 'COVAR_SAMP',
    'DELETING', 'DETERMINISTIC', 'FALSE', 'INSERTING', 'OFFSET', 'OVER',
    'RDB$RECORD_VERSION', 'REGR_AVGX', 'REGR_AVGY', 'REGR_COUNT', 'REGR_INTERCEPT',
    'REGR_R2', 'REGR_SLOPE', 'REGR_SXX', 'REGR_SXY', 'REGR_SYY', 'RETURN', 'ROW',
    'SCROLL', 'SQLSTATE', 'STDDEV_POP', 'STDDEV_SAMP', 'TRUE', 'UNKNOWN',
    'UPDATING', 'VAR_POP', 'VAR_SAMP'];
  FB_RES40: array of string = ['BINARY', 'DECFLOAT', 'INT128', 'LOCAL', 'LOCALTIME',
    'LOCALTIMESTAMP', 'PUBLICATION', 'RESETTING', 'TIMEZONE_HOUR',
    'TIMEZONE_MINUTE', 'UNBOUNDED', 'VARBINARY', 'WINDOW', 'WITHOUT'];

  SevText: array[TFBSeverity] of string = ('ERRO', 'AVISO', 'INFO');

  FIX_DIALECT = 'No FireDAC o parametro correto e SQLDialect=3 (Params do TFDConnection ou ' +
    'FDConnectionDefs.ini); "Dialect" nao e reconhecido. Confirme tambem que o proprio banco ' +
    'esta em dialeto 3: "select MON$SQL_DIALECT from MON$DATABASE". Se o banco estiver ' +
    'em dialeto 1, converta com: gfix -sql_dialect 3 <banco> (revise DATE/NUMERIC/aspas duplas antes).';
  FIX_RO = 'Defina ReadOnly=False e execute o DDL numa transacao de escrita ' +
    '(TxOptions.ReadOnly / TFDTransaction.Options.ReadOnly = False).';
  FIX_DDL = 'DDL exige transacao de escrita, banco em dialeto 3 e Commit logo apos executar. ' +
    'Prefira TFDScript (ou um TFDCommand por comando) separado dos comandos de dados.';
  FIX_TZ = 'No Firebird 4+ CURRENT_TIMESTAMP/CURRENT_TIME retornam TIMESTAMP/TIME WITH TIME ZONE. ' +
    'Use LOCALTIMESTAMP/LOCALTIME, ou DataTypeCompatibility = 3.0 no firebird.conf, ou execute ' +
    '"SET BIND OF TIME ZONE TO LEGACY" no FDConnection.AfterConnect.';
  FIX_INT128 = 'No Firebird 4+ SUM/AVG (e multiplicacoes) de BIGINT/NUMERIC(18,x) retornam ' +
    'INT128/NUMERIC(38,x); campos persistentes TLargeintField/TBCDField/TFMTBCDField geram ' +
    '"Type mismatch". Use CAST(SUM(...) AS NUMERIC(18,x)), "SET BIND OF INT128 TO LEGACY" / ' +
    '"SET BIND OF DECFLOAT TO LEGACY" no AfterConnect, ou DataTypeCompatibility = 3.0.';
  FIX_UDF = 'Firebird 4/5: UDFs estao desabilitadas por padrao (UdfAccess = None) e sao obsoletas. ' +
    'Troque por funcoes nativas ou reescreva como funcao PSQL/UDR. Paliativo: ' +
    'UdfAccess = Restrict UDF no firebird.conf, com DLL de 64/32 bits igual ao servidor.';
  FIX_RESERVED = 'Renomeie o objeto ou passe a usa-lo entre aspas duplas e em maiusculas ' +
    '("NOME") em todo SQL/PSQL. Para colunas: ALTER TABLE T ALTER COLUMN NOME TO NOVO_NOME ' +
    '(faca no 2.5, antes do backup).';
  MSG_RC = 'Firebird 4+ usa READ COMMITTED READ CONSISTENCY por padrao (ReadConsistency = 1).';
  FIX_RC = 'O padrao do FireDAC (xiReadCommitted) passa a ter leitura consistente por instrucao; ' +
    'REC_VERSION/NO_REC_VERSION sao ignorados e UPDATE/DELETE em conflito podem ser reiniciados ' +
    'internamente. Revise rotinas que dependiam de esperar locks/ler versoes recentes, ou ' +
    'ajuste ReadConsistency no firebird.conf.';

var
  GRxResCtx1, GRxResCtx2, GRxResCtx3, GResInList: string;

procedure Register;
begin
  RegisterComponents('Diagnostico', [TFBMetaScanner]);
end;

{ ---------------------------- helpers de arquivo ---------------------------- }

function GetFileVer(const AFile: string; out AMajor, AMinor, ARel, ABuild: Word): Boolean;
var
  Sz, H: DWORD;
  Buf: TBytes;
  P: Pointer;
  Len: UINT;
  Info: PVSFixedFileInfo;
begin
  Result := False;
  Sz := GetFileVersionInfoSize(PChar(AFile), H);
  if Sz = 0 then Exit;
  SetLength(Buf, Sz);
  if not GetFileVersionInfo(PChar(AFile), 0, Sz, @Buf[0]) then Exit;
  if not VerQueryValue(@Buf[0], '\', P, Len) then Exit;
  Info := PVSFixedFileInfo(P);
  AMajor := HiWord(Info^.dwFileVersionMS);
  AMinor := LoWord(Info^.dwFileVersionMS);
  ARel := HiWord(Info^.dwFileVersionLS);
  ABuild := LoWord(Info^.dwFileVersionLS);
  Result := True;
end;

function GetPEBits(const AFile: string): Integer;
var
  FS: TFileStream;
  Off: Int32;
  Sig: UInt32;
  Mach: UInt16;
begin
  Result := 0;
  try
    FS := TFileStream.Create(AFile, fmOpenRead or fmShareDenyNone);
    try
      FS.Position := $3C;
      FS.ReadBuffer(Off, 4);
      FS.Position := Off;
      FS.ReadBuffer(Sig, 4);
      if Sig <> $00004550 then Exit;
      FS.ReadBuffer(Mach, 2);
      case Mach of
        $014C: Result := 32;
        $8664: Result := 64;
      end;
    finally
      FS.Free;
    end;
  except
    Result := 0;
  end;
end;

function IsBinaryDfm(const AFile: string): Boolean;
var
  FS: TFileStream;
  Sig: array[0..3] of AnsiChar;
begin
  Result := False;
  try
    FS := TFileStream.Create(AFile, fmOpenRead or fmShareDenyNone);
    try
      if FS.Size < 4 then Exit;
      FS.ReadBuffer(Sig, 4);
      Result := (Sig[0] = 'T') and (Sig[1] = 'P') and (Sig[2] = 'F') and (Sig[3] = '0');
    finally
      FS.Free;
    end;
  except
    Result := False;
  end;
end;

function IsIBXClass(const ACls: string): Boolean;
begin
  Result := MatchText(ACls, ['TFDPhysIBDriverLink', 'TIBDatabase', 'TIBTransaction',
    'TIBQuery', 'TIBSQL', 'TIBDataSet', 'TIBTable', 'TIBStoredProc', 'TIBUpdateSQL']);
end;

function IsRelevantClass(const ACls: string): Boolean;
begin
  Result := MatchText(ACls, ['TFDConnection', 'TFDTransaction',
    'TFDPhysFBDriverLink', 'TFDQuery', 'TFDCommand', 'TFDScript',
    'TFDUpdateSQL', 'TFDStoredProc', 'TFDTable']) or IsIBXClass(ACls);
end;

function LineOf(ABase, AIndex: Integer): Integer;
begin
  if ABase <= 0 then Result := 0 else Result := ABase + AIndex;
end;

/// Retorna apenas o conteudo dos literais '...' de uma linha Pascal/DFM
function ExtractLiterals(const S: string): string;
var
  i: Integer;
  InStr: Boolean;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create;
  try
    InStr := False;
    i := 1;
    while i <= Length(S) do
    begin
      if S[i] = '''' then
      begin
        if InStr and (i < Length(S)) and (S[i + 1] = '''') then
        begin
          SB.Append('''');
          Inc(i, 2);
          Continue;
        end;
        InStr := not InStr;
        if not InStr then SB.Append(' ');
      end
      else if InStr then
        SB.Append(S[i])
      else if (S[i] = '/') and (i < Length(S)) and (S[i + 1] = '/') then
        Break;
      Inc(i);
    end;
    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

function LiteralsOf(ALines: TStrings): string;
var
  i: Integer;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create;
  try
    for i := 0 to ALines.Count - 1 do
      SB.Append(ExtractLiterals(ALines[i])).Append(sLineBreak);
    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

function StripSqlComment(const S: string): string;
var
  P: Integer;
begin
  P := Pos('--', S);
  if P > 0 then Result := Copy(S, 1, P - 1) else Result := S;
end;

function NormKV(const S: string): string;
var
  P: Integer;
begin
  P := Pos('=', S);
  if P = 0 then Exit(Trim(S));
  Result := Trim(Copy(S, 1, P - 1)) + '=' + Trim(Copy(S, P + 1, MaxInt));
end;

function ResVersion(const AWord: string): string;
begin
  if MatchText(AWord, FB_RES40) then Result := '4.0' else Result := '3.0';
end;

function UdfReplacement(const AName: string): string;
begin
  case IndexText(AName, ['STRLEN', 'SUBSTRLEN', 'SUBSTR', 'LTRIM', 'RTRIM', 'DIV',
    'TRUNCATE', 'I64TRUNCATE', 'I64ROUND', 'DPOWER', 'SRIGHT', 'STRING2BLOB',
    'DOW', 'SDOW', 'GETEXACTTIMESTAMP']) of
    0: Result := 'CHAR_LENGTH(x)';
    1: Result := 'SUBSTRING(x FROM inicio FOR tamanho)';
    2: Result := 'SUBSTRING(x FROM inicio FOR tamanho) (atencao: SUBSTR usa posicao FINAL)';
    3: Result := 'TRIM(LEADING FROM x)';
    4: Result := 'TRIM(TRAILING FROM x)';
    5: Result := 'divisao inteira nativa (a / b com inteiros em dialeto 3) ou TRUNC(a / b)';
    6, 7: Result := 'TRUNC(x)';
    8: Result := 'ROUND(x, n)';
    9: Result := 'POWER(x, y)';
    10: Result := 'RIGHT(x, n)';
    11: Result := 'CAST(x AS BLOB SUB_TYPE TEXT)';
    12, 13: Result := 'EXTRACT(WEEKDAY FROM x)';
    14: Result := 'LOCALTIMESTAMP';
  else
    if StartsText('ADD', AName) then
      Result := 'DATEADD(n DAY/MONTH/YEAR/HOUR/MINUTE/SECOND/WEEK/MILLISECOND TO data)'
    else if ContainsText(AName, 'NULLIF') then
      Result := 'NULLIF(a, b)'
    else if ContainsText(AName, 'NVL') then
      Result := 'COALESCE(a, b)'
    else
      Result := 'funcao nativa equivalente ou funcao PSQL/UDR';
  end;
end;

function OdsName(AMajor, AMinor: Integer): string;
begin
  case AMajor of
    10: Result := '1.x';
    11: case AMinor of
          0: Result := '2.0';
          1: Result := '2.1';
        else
          Result := '2.5';
        end;
    12: Result := '3.0';
    13: if AMinor = 0 then Result := '4.0' else Result := '5.0';
  else
    Result := '?';
  end;
end;

function DiagnoseConnectError(const AMsg: string): string;
begin
  if ContainsText(AMsg, 'wire encryption') then
    Result := 'Cliente antigo (fbclient 2.5) ou WireCrypt = Required no servidor. Use a fbclient.dll ' +
      'do FB5 ou ajuste WireCrypt = Enabled no firebird.conf.'
  else if ContainsText(AMsg, 'user name and password') then
    Result := 'Usuario nao existe no security5.fdb (Srp) ou so existe em Legacy_Auth. Usuarios do ' +
      'security2.fdb nao sao migrados: CREATE USER ... PASSWORD ''...'' USING PLUGIN Srp, ou ' +
      'AuthServer = Srp, Legacy_Auth + UserManager = Srp, Legacy_UserManager no firebird.conf.'
  else if ContainsText(AMsg, 'on-disk structure') or ContainsText(AMsg, 'ODS') then
    Result := 'Arquivo em ODS antiga: faca backup com gbak 2.5 (gbak -b -g) e restore com gbak 5.0.'
  else if ContainsText(AMsg, 'plugin') or ContainsText(AMsg, 'Engine') then
    Result := 'Embedded/plugins: copie plugins\engine13.dll, icu*.dll, firebird.msg e firebird.conf ' +
      'do FB5 junto da fbclient.dll, ou defina Server=localhost para usar o servico.'
  else if ContainsText(AMsg, 'security context') then
    Result := 'AuthClient/AuthServer incompativeis (ou OSAuthent sem Win_Sspi). Ajuste o firebird.conf.'
  else if ContainsText(AMsg, 'transliterate') or ContainsText(AMsg, 'Malformed string') then
    Result := 'Charset: defina CharacterSet na conexao igual ao dos dados (ex.: WIN1252/UTF8).'
  else if ContainsText(AMsg, 'unavailable database') or ContainsText(AMsg, 'network') then
    Result := 'Servico nao encontrado: confira Server/Port/Protocol (WNET/NetBEUI removido no FB5).'
  else
    Result := 'Verifique Server, Database, usuario/senha (Srp) e a fbclient.dll do FB5.';
end;

procedure BuildReservedPatterns;
var
  W, Alt, InL: string;
  procedure AddWord(const AW: string);
  begin
    if Alt <> '' then Alt := Alt + '|';
    Alt := Alt + StringReplace(AW, '$', '\$', [rfReplaceAll]);
    if InL <> '' then InL := InL + ',';
    InL := InL + '''' + AW + '''';
  end;
begin
  Alt := '';
  InL := '';
  for W in FB_RES30 do AddWord(W);
  for W in FB_RES40 do AddWord(W);
  // tabela.COLUNA, alias AS X, ORDER/GROUP BY X, DOMAIN X, TABLE X, VARIABLE X...
  GRxResCtx1 := '(?:\.\s*|\bAS\s+|\bBY\s+|\bDOMAIN\s+|\bTABLE\s+|\bCOLUMN\s+|\bVARIABLE\s+|' +
    '\bINTO\s+|\bFROM\s+|\bJOIN\s+|\bUPDATE\s+)(' + Alt + ')\b(?!\s*[\(\)])';
  // definicao de coluna: , X INTEGER / ( X VARCHAR / ADD X ...
  GRxResCtx2 := '(?:^|[,(]|\bADD\b)\s*(' + Alt + ')\s+(?:SMALLINT|INTEGER|INT|BIGINT|CHAR|' +
    'CHARACTER|VARCHAR|NUMERIC|DECIMAL|DATE|TIME|TIMESTAMP|FLOAT|DOUBLE|BLOB|TYPE\s+OF)\b';
  // comparacao/atribuicao: X = ... / SET X = ...
  GRxResCtx3 := '(?<![\.:\w$"])(' + Alt + ')\s*(?:=|<>|!=|>=|<=)(?!=)';
  GResInList := InL;
end;

{ ------------------------------ TFBMetaScanner ------------------------------ }

constructor TFBMetaScanner.Create(AOwner: TComponent);
begin
  inherited Create(AOwner);
  FFindings := TList<TFBFinding>.Create;
  FSeen := TList<TComponent>.Create;
  FReported := TDictionary<string, Boolean>.Create;
  FIncludeDataModules := True;

  Width := 860;
  Height := 440;
  BevelOuter := bvNone;
  Caption := '';
  ShowCaption := False;

  FTop := TPanel.Create(Self);
  FTop.Parent := Self;
  FTop.Align := alTop;
  FTop.Height := 36;
  FTop.BevelOuter := bvNone;
  FTop.Caption := '';
  FTop.ShowCaption := False;

  FBtnForm := MakeButton('Varrer Form', 6, 100, BtnFormClick);
  FBtnUnit := MakeButton('Varrer Unit...', 112, 110, BtnUnitClick);
  FBtnProject := MakeButton('Varrer Projeto...', 228, 120, BtnProjectClick);
  FBtnDB := MakeButton('Varrer Banco', 354, 100, BtnDBClick);
  FBtnCopy := MakeButton('Copiar', 460, 70, BtnCopyClick);
  FBtnClear := MakeButton('Limpar', 536, 70, BtnClearClick);

  FStatus := TLabel.Create(Self);
  FStatus.Parent := FTop;
  FStatus.Left := 618;
  FStatus.Top := 11;
  FStatus.Caption := 'Pronto.';

  FDetail := TMemo.Create(Self);
  FDetail.Parent := Self;
  FDetail.Align := alBottom;
  FDetail.Height := 110;
  FDetail.ReadOnly := True;
  FDetail.ScrollBars := ssVertical;
  FDetail.WordWrap := True;

  FList := TListView.Create(Self);
  FList.Parent := Self;
  FList.Align := alClient;
  FList.ViewStyle := vsReport;
  FList.ReadOnly := True;
  FList.RowSelect := True;
  FList.GridLines := True;
  FList.HideSelection := False;
  with FList.Columns.Add do begin Caption := 'Sev.'; Width := 60; end;
  with FList.Columns.Add do begin Caption := 'Local'; Width := 230; end;
  with FList.Columns.Add do begin Caption := 'Linha'; Width := 50; end;
  with FList.Columns.Add do begin Caption := 'Problema'; Width := 480; end;
  FList.OnSelectItem := ListSelectItem;
  FList.OnCustomDrawItem := ListCustomDrawItem;
end;

destructor TFBMetaScanner.Destroy;
begin
  FReported.Free;
  FSeen.Free;
  FFindings.Free;
  inherited;
end;

function TFBMetaScanner.MakeButton(const ACaption: string; ALeft, AWidth: Integer;
  AHandler: TNotifyEvent): TButton;
begin
  Result := TButton.Create(Self);
  Result.Parent := FTop;
  Result.SetBounds(ALeft, 5, AWidth, 26);
  Result.Caption := ACaption;
  Result.OnClick := AHandler;
end;

procedure TFBMetaScanner.Notification(AComponent: TComponent; Operation: TOperation);
begin
  inherited;
  if Operation = opRemove then
  begin
    if AComponent = FConnection then FConnection := nil;
    if AComponent = FTargetForm then FTargetForm := nil;
  end;
end;

procedure TFBMetaScanner.SetConnection(const Value: TFDConnection);
begin
  if FConnection <> Value then
  begin
    FConnection := Value;
    if Value <> nil then Value.FreeNotification(Self);
  end;
end;

procedure TFBMetaScanner.SetTargetForm(const Value: TCustomForm);
begin
  if FTargetForm <> Value then
  begin
    FTargetForm := Value;
    if Value <> nil then Value.FreeNotification(Self);
  end;
end;

{ ------------------------------- botoes / UI -------------------------------- }

procedure TFBMetaScanner.BtnFormClick(Sender: TObject);
begin
  ScanForm;
end;

procedure TFBMetaScanner.BtnUnitClick(Sender: TObject);
begin
  ScanUnit('');
end;

procedure TFBMetaScanner.BtnProjectClick(Sender: TObject);
begin
  ScanProject('');
end;

procedure TFBMetaScanner.BtnDBClick(Sender: TObject);
begin
  ScanDatabase(nil);
end;

procedure TFBMetaScanner.BtnCopyClick(Sender: TObject);
begin
  Clipboard.AsText := ReportText;
  FStatus.Caption := 'Relatorio copiado para a area de transferencia.';
end;

procedure TFBMetaScanner.BtnClearClick(Sender: TObject);
begin
  Clear;
end;

procedure TFBMetaScanner.ListSelectItem(Sender: TObject; Item: TListItem;
  Selected: Boolean);
var
  F: TFBFinding;
begin
  if not Selected or (Item = nil) then Exit;
  F := FFindings[Integer(NativeInt(Item.Data))];
  FDetail.Text := F.Msg + sLineBreak + sLineBreak + 'Como corrigir: ' + F.Fix;
end;

procedure TFBMetaScanner.ListCustomDrawItem(Sender: TCustomListView; Item: TListItem;
  State: TCustomDrawState; var DefaultDraw: Boolean);
begin
  case FFindings[Integer(NativeInt(Item.Data))].Severity of
    fsError: Sender.Canvas.Font.Color := clRed;
    fsWarning: Sender.Canvas.Font.Color := clWebDarkOrange;
    fsInfo: Sender.Canvas.Font.Color := clNavy;
  end;
end;

procedure TFBMetaScanner.SetBusy(ABusy: Boolean; const AText: string);
begin
  FTop.Enabled := not ABusy;
  if AText <> '' then FStatus.Caption := AText;
  if ABusy then Application.ProcessMessages;
end;

procedure TFBMetaScanner.AddFinding(ASev: TFBSeverity; const ASource: string;
  ALine: Integer; const AMsg, AFix: string);
var
  F: TFBFinding;
begin
  F.Severity := ASev;
  F.Source := ASource;
  F.Line := ALine;
  F.Msg := AMsg;
  F.Fix := AFix;
  FFindings.Add(F);
end;

function TFBMetaScanner.Once(const AKey: string): Boolean;
var
  K: string;
begin
  K := UpperCase(AKey);
  Result := not FReported.ContainsKey(K);
  if Result then FReported.Add(K, True);
end;

procedure TFBMetaScanner.Clear;
begin
  FFindings.Clear;
  FSeen.Clear;
  FReported.Clear;
  FList.Items.Clear;
  FDetail.Clear;
  FStatus.Caption := 'Pronto.';
end;

procedure TFBMetaScanner.BeginScan;
begin
  Clear;
  FFoundFBConn := False;
  FFoundLink := False;
  FCurSource := '';
  FRootDir := '';
end;

procedure TFBMetaScanner.RefreshList;
var
  i: Integer;
  F: TFBFinding;
begin
  FFindings.Sort(TComparer<TFBFinding>.Construct(
    function(const A, B: TFBFinding): Integer
    begin
      Result := Ord(A.Severity) - Ord(B.Severity);
      if Result = 0 then Result := CompareText(A.Source, B.Source);
      if Result = 0 then Result := A.Line - B.Line;
    end));
  FList.Items.BeginUpdate;
  try
    FList.Items.Clear;
    for i := 0 to FFindings.Count - 1 do
    begin
      F := FFindings[i];
      with FList.Items.Add do
      begin
        Caption := SevText[F.Severity];
        SubItems.Add(F.Source);
        if F.Line > 0 then SubItems.Add(IntToStr(F.Line)) else SubItems.Add('');
        SubItems.Add(F.Msg);
        Data := Pointer(NativeInt(i));
      end;
    end;
  finally
    FList.Items.EndUpdate;
  end;
end;

procedure TFBMetaScanner.EndScan;
var
  E, W, I: Integer;
  F: TFBFinding;
begin
  E := 0; W := 0; I := 0;
  for F in FFindings do
    case F.Severity of
      fsError: Inc(E);
      fsWarning: Inc(W);
    else
      Inc(I);
    end;
  if (E = 0) and (W = 0) then
    AddFinding(fsInfo, 'Resumo', 0,
      'Nenhum problema obvio encontrado nesta varredura.',
      'Use tambem "Varrer Banco" conectado ao banco 2.5 (antes do backup) e ao 5.0 (apos o ' +
      'restore): ele analisa ODS, UDFs, nomes reservados e o fonte de procedures/triggers/views. ' +
      'Se o erro -817 persistir, logue o SQL exato que o dispara (DDL ou UPDATE/INSERT em RDB$).');
  RefreshList;
  SetBusy(False, Format('%d erro(s), %d aviso(s), %d info.', [E, W, I]));
  if FList.Items.Count > 0 then
    FList.Items[0].Selected := True;
end;

function TFBMetaScanner.ErrorCount: Integer;
var
  F: TFBFinding;
begin
  Result := 0;
  for F in FFindings do
    if F.Severity = fsError then Inc(Result);
end;

function TFBMetaScanner.ReportText: string;
var
  SL: TStringList;
  F: TFBFinding;
begin
  SL := TStringList.Create;
  try
    for F in FFindings do
    begin
      if F.Line > 0 then
        SL.Add(Format('[%s] %s (linha %d): %s', [SevText[F.Severity], F.Source, F.Line, F.Msg]))
      else
        SL.Add(Format('[%s] %s: %s', [SevText[F.Severity], F.Source, F.Msg]));
      SL.Add('    -> ' + F.Fix);
    end;
    Result := SL.Text;
  finally
    SL.Free;
  end;
end;

{ ------------------------------ varredura viva ------------------------------ }

procedure TFBMetaScanner.ScanForm;
var
  F: TCustomForm;
  i: Integer;
begin
  BeginScan;
  SetBusy(True, 'Analisando componentes do form...');
  try
    F := FTargetForm;
    if F = nil then F := GetParentForm(Self);
    if F <> nil then ScanComponents(F, F.Name)
    else AddFinding(fsInfo, 'Form', 0, 'Nenhum form alvo encontrado.',
      'Defina a propriedade TargetForm ou coloque o componente dentro de um form.');

    if FIncludeDataModules then
      for i := 0 to Screen.DataModuleCount - 1 do
        ScanComponents(Screen.DataModules[i], Screen.DataModules[i].Name);

    if FConnection <> nil then
      CheckComponent(FConnection, FConnection.Name);

    CheckLoadedClient;
  finally
    EndScan;
  end;
end;

function TFBMetaScanner.FindFirstConnection: TFDConnection;

  function FindIn(AOwner: TComponent): TFDConnection;
  var
    i: Integer;
  begin
    Result := nil;
    if AOwner = nil then Exit;
    for i := 0 to AOwner.ComponentCount - 1 do
    begin
      if AOwner.Components[i] is TFDConnection then
        Exit(TFDConnection(AOwner.Components[i]));
      if AOwner.Components[i] is TFrame then
      begin
        Result := FindIn(AOwner.Components[i]);
        if Result <> nil then Exit;
      end;
    end;
  end;

var
  F: TCustomForm;
  i: Integer;
begin
  F := FTargetForm;
  if F = nil then F := GetParentForm(Self);
  Result := FindIn(F);
  if Result = nil then
    for i := 0 to Screen.DataModuleCount - 1 do
    begin
      Result := FindIn(Screen.DataModules[i]);
      if Result <> nil then Exit;
    end;
end;

procedure TFBMetaScanner.ScanDatabase(AConn: TFDConnection);
var
  C: TFDConnection;
begin
  C := AConn;
  if C = nil then C := FConnection;
  if C = nil then C := FindFirstConnection;
  BeginScan;
  SetBusy(True, 'Analisando banco...');
  try
    if C = nil then
    begin
      AddFinding(fsInfo, 'Banco', 0, 'Nenhuma TFDConnection encontrada.',
        'Defina a propriedade Connection ou coloque uma TFDConnection no form/DataModule.');
      Exit;
    end;
    if not C.Connected then
      if MessageDlg(Format('A conexao "%s" esta fechada. Conectar agora?', [C.Name]),
        mtConfirmation, [mbYes, mbNo], 0) = mrYes then
      try
        C.Connected := True;
      except
        on E: Exception do
          AddFinding(fsError, C.Name, 0, 'Falha ao conectar: ' + E.Message,
            DiagnoseConnectError(E.Message));
      end;
    CheckComponent(C, C.Name);
    if not C.Connected then
      AddFinding(fsInfo, C.Name, 0, 'Conexao fechada: verificacoes no banco nao foram executadas.',
        'Conecte e varra novamente.');
    CheckLoadedClient;
  finally
    EndScan;
  end;
end;

procedure TFBMetaScanner.ScanComponents(AOwner: TComponent; const APath: string);
var
  i: Integer;
  C: TComponent;
begin
  for i := 0 to AOwner.ComponentCount - 1 do
  begin
    C := AOwner.Components[i];
    if C is TFrame then
      ScanComponents(C, APath + '.' + C.Name)
    else
      CheckComponent(C, APath + '.' + C.Name);
  end;
end;

procedure TFBMetaScanner.CheckComponent(C: TComponent; const AWhere: string);
var
  SL: TStringList;
  j: Integer;
  Q: TFDQuery;
begin
  if FSeen.IndexOf(C) >= 0 then Exit;
  FSeen.Add(C);

  if C is TFDConnection then
    CheckConnection(TFDConnection(C), AWhere)
  else if C is TFDTransaction then
    CheckTransaction(TFDTransaction(C), AWhere)
  else if C is TFDPhysFBDriverLink then
    CheckDriverLink(TFDPhysFBDriverLink(C), AWhere)
  else if C is TFDScript then
  begin
    SL := TStringList.Create;
    try
      for j := 0 to TFDScript(C).SQLScripts.Count - 1 do
        SL.AddStrings(TFDScript(C).SQLScripts[j].SQL);
      ScanSQLLines(SL, AWhere, 0, True, True);
      ScanMigration(SL, AWhere, 0, tmRaw, 0);
    finally
      SL.Free;
    end;
  end
  else if C is TFDQuery then
  begin
    Q := TFDQuery(C);
    ScanSQLLines(Q.SQL, AWhere, 0, True, False);
    ScanMigration(Q.SQL, AWhere, 0, tmRaw, 0);
    // campos persistentes: o dono dos fields e o form, nao o dataset
    if (Q.FieldCount > 0) and (Q.Fields[0].Owner <> Q) then
      CheckPersistentSQL(Q.SQL.Text, AWhere, 0);
  end
  else if C is TFDCommand then
  begin
    ScanSQLLines(TFDCommand(C).CommandText, AWhere, 0, True, False);
    ScanMigration(TFDCommand(C).CommandText, AWhere, 0, tmRaw, 0);
  end
  else if C is TFDUpdateSQL then
  begin
    SL := TStringList.Create;
    try
      SL.AddStrings(TFDUpdateSQL(C).InsertSQL);
      SL.AddStrings(TFDUpdateSQL(C).ModifySQL);
      SL.AddStrings(TFDUpdateSQL(C).DeleteSQL);
      SL.AddStrings(TFDUpdateSQL(C).LockSQL);
      SL.AddStrings(TFDUpdateSQL(C).UnlockSQL);
      SL.AddStrings(TFDUpdateSQL(C).FetchRowSQL);
      ScanMigration(SL, AWhere, 0, tmRaw, 0);
    finally
      SL.Free;
    end;
  end
  else if IsIBXClass(C.ClassName) then
    ReportIBX(C.ClassName, AWhere, 0);
end;

procedure TFBMetaScanner.ReportIBX(const ACls, AWhere: string; ALine: Integer);
begin
  if not Once(AWhere + '|IBX|' + ACls) then Exit;
  if SameText(ACls, 'TFDPhysIBDriverLink') then
    AddFinding(fsWarning, AWhere, ALine,
      'TFDPhysIBDriverLink (driver InterBase) em uso.',
      'Para Firebird 5 use TFDPhysFBDriverLink e DriverID=FB: o driver IB nao conhece BOOLEAN, ' +
      'INT128, DECFLOAT, TIME ZONE nem a autenticacao Srp.')
  else
    AddFinding(fsWarning, AWhere, ALine,
      Format('Componente IBX (%s) em uso.', [ACls]),
      'IBX e voltado ao InterBase e nao suporta oficialmente Firebird 3+ (Srp, BOOLEAN, INT128, ' +
      'TIME ZONE). Migre para FireDAC (TFDConnection/TFDQuery com DriverID=FB).');
end;

procedure TFBMetaScanner.ReportReadConsistency(const AWhere: string; ALine: Integer);
begin
  if Once('GLOBAL|READCONSISTENCY') then
    AddFinding(fsInfo, AWhere, ALine, MSG_RC, FIX_RC);
end;

procedure TFBMetaScanner.CheckFBParams(AParams: TStrings; const ADriver, AWhere: string;
  ALine: Integer);
var
  Drv, D, DOld, CS, Pw, Proto, Db, Srv, Adv: string;
begin
  Drv := ADriver;
  if Drv = '' then Drv := Trim(AParams.Values['DriverID']);
  if SameText(Drv, 'IB') then
    AddFinding(fsWarning, AWhere, ALine,
      'DriverID=IB (InterBase). Se o servidor for Firebird, o driver correto e FB.',
      'Use DriverID=FB com TFDPhysFBDriverLink: o driver IB nao conhece BOOLEAN, INT128, ' +
      'DECFLOAT, TIME ZONE nem a autenticacao Srp.');

  // dialeto
  D := Trim(AParams.Values['SQLDialect']);
  DOld := Trim(AParams.Values['Dialect']);
  if DOld <> '' then
  begin
    if D = '' then
      AddFinding(fsWarning, AWhere, ALine,
        Format('Parametro "Dialect=%s" nao e reconhecido pelo FireDAC (e ignorado); ' +
          'o nome correto e SQLDialect.', [DOld]), FIX_DIALECT)
    else
      AddFinding(fsInfo, AWhere, ALine,
        'Parametro "Dialect" e redundante (o FireDAC usa apenas SQLDialect).',
        'Remova a linha Dialect=... para evitar confusao.');
  end;
  if D = '' then
  begin
    if DOld = '' then
      AddFinding(fsInfo, AWhere, ALine,
        'SQLDialect nao definido (o FireDAC usa 3 por padrao).',
        'Opcional: declare SQLDialect=3 explicitamente. ' + FIX_DIALECT);
  end
  else if D <> '3' then
    AddFinding(fsError, AWhere, ALine,
      Format('SQLDialect=%s na conexao. O Firebird 5 deve ser usado com SQLDialect=3.', [D]),
      FIX_DIALECT);

  Adv := AParams.Values['IBAdvanced'];
  if TRegEx.IsMatch(Adv, 'sql_dialect\s*=\s*[12]', [roIgnoreCase]) then
    AddFinding(fsError, AWhere, ALine, 'IBAdvanced forca sql_dialect 1/2.', FIX_DIALECT);

  // charset
  CS := Trim(AParams.Values['CharacterSet']);
  if CS = '' then
    AddFinding(fsWarning, AWhere, ALine, 'CharacterSet nao definido na conexao.',
      'Defina CharacterSet igual ao charset dos dados (ex.: WIN1252 ou UTF8). No FB3+ conexoes ' +
      'NONE geram "Malformed string"/"Cannot transliterate" com acentos.')
  else if SameText(CS, 'NONE') then
    AddFinding(fsWarning, AWhere, ALine, 'CharacterSet=NONE na conexao.',
      'No FB3+ use o charset real dos dados (ex.: WIN1252/UTF8) para evitar erros de transliteracao.');

  // autenticacao
  Pw := AParams.Values['Password'];
  if Length(Pw) > 8 then
    AddFinding(fsWarning, AWhere, ALine,
      Format('Senha com %d caracteres (> 8).', [Length(Pw)]),
      'No FB 2.5 (Legacy_Auth) so os 8 primeiros caracteres eram validados; no FB5 (Srp) a senha ' +
      'inteira e comparada. Confirme a senha cadastrada no servidor novo.');
  if SameText(Trim(AParams.Values['OSAuthent']), 'Yes') then
    AddFinding(fsInfo, AWhere, ALine, 'OSAuthent=Yes (autenticacao do Windows).',
      'No FB3+ exige Win_Sspi em AuthServer/AuthClient e CREATE MAPPING para o usuario do Windows.');

  // protocolo / servidor
  Proto := Trim(AParams.Values['Protocol']);
  Db := Trim(AParams.Values['Database']);
  Srv := Trim(AParams.Values['Server']);
  if SameText(Proto, 'NetBEUI') or StartsStr('\\', Db) then
    AddFinding(fsError, AWhere, ALine,
      'Protocolo NetBEUI/WNET (named pipes, \\servidor\...) em uso.',
      'O WNET foi removido no Firebird 5. Use Protocol=TCPIP com Server=<host> (ou Local/XNET).');
  if (Srv = '') and ((Proto = '') or SameText(Proto, 'Local')) and (Db <> '') and
     not TRegEx.IsMatch(Db, '^[\w\.\-]{2,}(/\d+)?:') and not StartsStr('\\', Db) then
    AddFinding(fsInfo, AWhere, ALine, 'Conexao local sem Server definido.',
      'No FB3+ a fbclient tenta primeiro o modo embedded (plugins\engine13.dll) e so depois XNET. ' +
      'Defina Server=localhost (Protocol=TCPIP) para garantir o uso do servico Firebird 5.');
end;

procedure TFBMetaScanner.CheckConnection(AConn: TFDConnection; const AWhere: string);
var
  Drv: string;
begin
  Drv := Trim(AConn.Params.Values['DriverID']);
  if Drv = '' then Drv := Trim(AConn.DriverName);
  if (Drv <> '') and not SameText(Drv, 'FB') and not SameText(Drv, 'IB') then Exit;
  FFoundFBConn := True;

  if AConn.ConnectionDefName <> '' then
    AddFinding(fsInfo, AWhere, 0,
      Format('A conexao usa ConnectionDefName "%s": SQLDialect e demais parametros vem do ' +
        'FDConnectionDefs.ini.', [AConn.ConnectionDefName]),
      'Confira se a definicao tem SQLDialect=3 (e execute a varredura de Projeto para ler o .ini).')
  else
    CheckFBParams(AConn.Params, Drv, AWhere, 0);

  if AConn.TxOptions.ReadOnly then
    AddFinding(fsError, AWhere, 0,
      'TxOptions.ReadOnly = True: a transacao padrao e somente leitura e bloqueia DDL.',
      FIX_RO);
  if AConn.UpdateOptions.ReadOnly then
    AddFinding(fsWarning, AWhere, 0,
      'UpdateOptions.ReadOnly = True na conexao.', FIX_RO);
  if Assigned(AConn.Transaction) and AConn.Transaction.Options.ReadOnly then
    AddFinding(fsError, AWhere, 0,
      'A transacao associada (Connection.Transaction) esta com Options.ReadOnly = True.',
      FIX_RO);
  if not AConn.TxOptions.AutoCommit then
    AddFinding(fsInfo, AWhere, 0,
      'TxOptions.AutoCommit = False: DDL so e efetivado apos Commit explicito.',
      'Chame Connection.Commit logo apos cada DDL, antes de usar o novo objeto em DML.');
  if AConn.TxOptions.Isolation = xiReadCommitted then
    ReportReadConsistency(AWhere, 0);

  if AConn.Connected then
  begin
    CheckLiveDatabase(AConn, AWhere);
    CheckLiveMigration(AConn, AWhere);
    ScanDbSources(AConn, AWhere);
  end;
end;

procedure TFBMetaScanner.CheckLiveDatabase(AConn: TFDConnection; const AWhere: string);
var
  V: Variant;
  Dlg: Integer;
begin
  try
    V := AConn.ExecSQLScalar('select MON$SQL_DIALECT from MON$DATABASE');
    if not VarIsNull(V) then
    begin
      Dlg := V;
      if Dlg <> 3 then
        AddFinding(fsError, AWhere, 0,
          Format('O BANCO conectado esta em dialeto %d (MON$SQL_DIALECT).', [Dlg]), FIX_DIALECT)
      else
        AddFinding(fsInfo, AWhere, 0, 'Banco conectado em dialeto 3 (OK).', 'Nada a fazer.');
    end;

    V := AConn.ExecSQLScalar('select MON$READ_ONLY from MON$DATABASE');
    if (not VarIsNull(V)) and (Integer(V) = 1) then
      AddFinding(fsError, AWhere, 0, 'O banco esta em modo READ ONLY.',
        'Use: gfix -mode read_write <banco> (com acesso exclusivo).');

    V := AConn.ExecSQLScalar('select MON$READ_ONLY from MON$TRANSACTIONS ' +
      'where MON$TRANSACTION_ID = current_transaction');
    if (not VarIsNull(V)) and (Integer(V) = 1) then
      AddFinding(fsError, AWhere, 0, 'A transacao atual esta READ ONLY (verificado no servidor).',
        FIX_RO);

    V := AConn.ExecSQLScalar('select rdb$get_context(''SYSTEM'',''ENGINE_VERSION'') from rdb$database');
    if not VarIsNull(V) then
      AddFinding(fsInfo, AWhere, 0, 'Versao do servidor Firebird: ' + VarToStr(V), 'Informativo.');
  except
    on E: Exception do
      AddFinding(fsInfo, AWhere, 0,
        'Nao foi possivel consultar o banco: ' + E.Message,
        'Verifique se o usuario pode ler as tabelas MON$.');
  end;
end;

function QueryRows(AConn: TFDConnection; const ASQL: string; ARows: TStrings): Boolean;
var
  Q: TFDQuery;
begin
  ARows.Clear;
  Q := TFDQuery.Create(nil);
  try
    Q.Connection := AConn;
    Q.ResourceOptions.MacroCreate := False;
    Q.ResourceOptions.MacroExpand := False;
    Q.ResourceOptions.ParamCreate := False;
    Q.ResourceOptions.EscapeExpand := False;
    Q.SQL.Text := ASQL;
    Q.Open;
    while not Q.Eof do
    begin
      ARows.Add(Trim(Q.Fields[0].AsString));
      Q.Next;
    end;
    Result := True;
  finally
    Q.Free;
  end;
end;

procedure TFBMetaScanner.CheckLiveMigration(AConn: TFDConnection; const AWhere: string);
var
  V, V2: Variant;
  Ma, Mi, i: Integer;
  S, L, Where: string;
  Rows: TStringList;

  function NameIn(const ACol: string): string;
  begin
    Result := 'trim(' + ACol + ') in (' + GResInList + ')';
  end;

begin
  Where := AWhere + ' > banco';
  Rows := TStringList.Create;
  try
    // ODS / formato do arquivo
    try
      V := AConn.ExecSQLScalar('select MON$ODS_MAJOR from MON$DATABASE');
      V2 := AConn.ExecSQLScalar('select MON$ODS_MINOR from MON$DATABASE');
      if not VarIsNull(V) then
      begin
        Ma := V;
        if VarIsNull(V2) then Mi := 0 else Mi := V2;
        if Ma < 13 then
          AddFinding(fsWarning, Where, 0,
            Format('Banco em ODS %d.%d (formato do Firebird %s).', [Ma, Mi, OdsName(Ma, Mi)]),
            'O Firebird 5 usa ODS 13.1: faca backup com o gbak da versao antiga (gbak -b -g) e ' +
            'restore com o gbak 5.0 (gbak -c). Usuarios do security2.fdb NAO sao migrados: ' +
            'recrie-os (plugin Srp). Corrija os erros desta lista antes do backup.')
        else
          AddFinding(fsInfo, Where, 0,
            Format('Banco em ODS %d.%d (Firebird %s).', [Ma, Mi, OdsName(Ma, Mi)]), 'Informativo.');
      end;
    except
      on E: Exception do
        AddFinding(fsInfo, Where, 0, 'Nao foi possivel ler a ODS: ' + E.Message, 'Informativo.');
    end;

    // charset padrao
    try
      V := AConn.ExecSQLScalar('select trim(RDB$CHARACTER_SET_NAME) from RDB$DATABASE');
      S := Trim(VarToStr(V));
      if (S = '') or SameText(S, 'NONE') then
        AddFinding(fsWarning, Where, 0, 'Charset padrao do banco e NONE.',
          'No FB3+ conversoes com NONE sao mais rigidas ("Malformed string"/"Cannot transliterate"). ' +
          'Defina CharacterSet na conexao igual ao dos dados (ex.: WIN1252) e, se preciso, use ' +
          'gbak -c -fix_fss_data <charset> -fix_fss_metadata <charset> no restore.')
      else
        AddFinding(fsInfo, Where, 0, 'Charset padrao do banco: ' + S + '.', 'Informativo.');
    except
      on E: Exception do ;
    end;

    // UDFs declaradas
    try
      QueryRows(AConn, 'select trim(RDB$FUNCTION_NAME) || '' ('' || coalesce(trim(RDB$MODULE_NAME), '''') || '')'' ' +
        'from RDB$FUNCTIONS where RDB$MODULE_NAME is not null and coalesce(RDB$SYSTEM_FLAG, 0) = 0 ' +
        'order by 1', Rows);
      if Rows.Count > 0 then
      begin
        L := '';
        for i := 0 to Rows.Count - 1 do
        begin
          if i = 40 then begin L := L + Format(', ... (+%d)', [Rows.Count - 40]); Break; end;
          if L <> '' then L := L + ', ';
          L := L + Rows[i];
        end;
        AddFinding(fsError, Where, 0,
          Format('%d UDF(s) externa(s) declarada(s) no banco: %s', [Rows.Count, L]), FIX_UDF);
      end;
    except
      on E: Exception do ;
    end;

    // tabelas externas
    try
      QueryRows(AConn, 'select trim(RDB$RELATION_NAME) from RDB$RELATIONS ' +
        'where RDB$EXTERNAL_FILE is not null', Rows);
      if Rows.Count > 0 then
        AddFinding(fsWarning, Where, 0,
          'Tabelas externas (EXTERNAL FILE): ' + Rows.CommaText,
          'FB3+: ExternalFileAccess = None por padrao. Configure ExternalFileAccess = Restrict <pasta> ' +
          'no firebird.conf.');
    except
      on E: Exception do ;
    end;

    // BLOB filters
    try
      QueryRows(AConn, 'select trim(RDB$FUNCTION_NAME) from RDB$FILTERS', Rows);
      if Rows.Count > 0 then
        AddFinding(fsWarning, Where, 0, 'BLOB filters externos: ' + Rows.CommaText,
          'Dependem de DLL externa compilada para a versao/arquitetura do servidor; recompile ou remova.');
    except
      on E: Exception do ;
    end;

    // objetos com nomes que viraram palavras reservadas
    try
      QueryRows(AConn,
        'select cast(''Tabela/View '' || trim(RDB$RELATION_NAME) as varchar(300)) from RDB$RELATIONS ' +
        'where coalesce(RDB$SYSTEM_FLAG, 0) = 0 and ' + NameIn('RDB$RELATION_NAME') +
        ' union all select cast(''Coluna '' || trim(RDB$RELATION_NAME) || ''.'' || trim(RDB$FIELD_NAME) as varchar(300)) ' +
        'from RDB$RELATION_FIELDS where coalesce(RDB$SYSTEM_FLAG, 0) = 0 and ' + NameIn('RDB$FIELD_NAME') +
        ' union all select cast(''Dominio '' || trim(RDB$FIELD_NAME) as varchar(300)) from RDB$FIELDS ' +
        'where coalesce(RDB$SYSTEM_FLAG, 0) = 0 and ' + NameIn('RDB$FIELD_NAME') +
        ' union all select cast(''Procedure '' || trim(RDB$PROCEDURE_NAME) as varchar(300)) from RDB$PROCEDURES ' +
        'where ' + NameIn('RDB$PROCEDURE_NAME') +
        ' union all select cast(''Parametro '' || trim(RDB$PROCEDURE_NAME) || ''.'' || trim(RDB$PARAMETER_NAME) as varchar(300)) ' +
        'from RDB$PROCEDURE_PARAMETERS where ' + NameIn('RDB$PARAMETER_NAME') +
        ' union all select cast(''Generator '' || trim(RDB$GENERATOR_NAME) as varchar(300)) from RDB$GENERATORS ' +
        'where ' + NameIn('RDB$GENERATOR_NAME') +
        ' union all select cast(''Exception '' || trim(RDB$EXCEPTION_NAME) as varchar(300)) from RDB$EXCEPTIONS ' +
        'where ' + NameIn('RDB$EXCEPTION_NAME') +
        ' union all select cast(''Indice '' || trim(RDB$INDEX_NAME) as varchar(300)) from RDB$INDICES ' +
        'where ' + NameIn('RDB$INDEX_NAME'), Rows);
      for i := 0 to Rows.Count - 1 do
      begin
        if i = 100 then
        begin
          AddFinding(fsError, Where, 0, Format('... mais %d objeto(s) com nome reservado.',
            [Rows.Count - 100]), FIX_RESERVED);
          Break;
        end;
        S := Rows[i];
        L := S.Substring(S.LastDelimiter(' .') + 1);
        AddFinding(fsError, Where, 0,
          Format('%s: nome e palavra reservada no Firebird %s+.', [S, ResVersion(L)]),
          'Todo SQL/PSQL que usar este nome sem aspas falhara no FB5. ' + FIX_RESERVED);
      end;
    except
      on E: Exception do
        AddFinding(fsInfo, Where, 0, 'Falha ao procurar nomes reservados: ' + E.Message, 'Informativo.');
    end;
  finally
    Rows.Free;
  end;
end;

procedure TFBMetaScanner.ScanDbSources(AConn: TFDConnection; const AWhere: string);
var
  Q: TFDQuery;
  SL: TStringList;

  procedure Run(const ASQL, AKind: string; AIsTrigger: Boolean);
  var
    Nm, W: string;
    Tp, Ctx: Integer;
  begin
    try
      Q.Close;
      Q.SQL.Text := ASQL;
      Q.Open;
      while not Q.Eof do
      begin
        Nm := Trim(Q.Fields[0].AsString);
        SL.Text := Q.Fields[1].AsString;
        Ctx := 0;
        if AIsTrigger then
        begin
          Tp := Q.Fields[2].AsInteger;
          // TRIGGER_ACTION_PREFIX: ((tipo + 1) and 1) = 1 -> AFTER
          if (Tp < 8192) and (((Tp + 1) and 1) = 1) then Ctx := 1 else Ctx := 2;
        end;
        W := AWhere + ' > ' + AKind + ' ' + Nm;
        ScanSQLLines(SL, W, 1, False, True);
        ScanMigration(SL, W, 1, tmRaw, Ctx);
        Q.Next;
      end;
    except
      on E: Exception do
        AddFinding(fsInfo, AWhere, 0, Format('Falha ao ler fontes (%s): %s', [AKind, E.Message]),
          'Informativo.');
    end;
  end;

begin
  Q := TFDQuery.Create(nil);
  SL := TStringList.Create;
  try
    Q.Connection := AConn;
    Q.ResourceOptions.MacroCreate := False;
    Q.ResourceOptions.MacroExpand := False;
    Q.ResourceOptions.ParamCreate := False;
    Q.ResourceOptions.EscapeExpand := False;
    Run('select RDB$PROCEDURE_NAME, RDB$PROCEDURE_SOURCE from RDB$PROCEDURES ' +
      'where coalesce(RDB$SYSTEM_FLAG, 0) = 0', 'PROCEDURE', False);
    Run('select RDB$TRIGGER_NAME, RDB$TRIGGER_SOURCE, RDB$TRIGGER_TYPE from RDB$TRIGGERS ' +
      'where coalesce(RDB$SYSTEM_FLAG, 0) = 0', 'TRIGGER', True);
    Run('select RDB$RELATION_NAME, RDB$VIEW_SOURCE from RDB$RELATIONS ' +
      'where RDB$VIEW_BLR is not null and coalesce(RDB$SYSTEM_FLAG, 0) = 0', 'VIEW', False);
    Run('select RDB$FIELD_NAME, RDB$COMPUTED_SOURCE from RDB$FIELDS ' +
      'where RDB$COMPUTED_SOURCE is not null and coalesce(RDB$SYSTEM_FLAG, 0) = 0', 'CAMPO CALCULADO', False);
  finally
    SL.Free;
    Q.Free;
  end;
end;

procedure TFBMetaScanner.CheckTransaction(ATx: TFDTransaction; const AWhere: string);
begin
  if ATx.Options.ReadOnly then
    AddFinding(fsError, AWhere, 0,
      'TFDTransaction.Options.ReadOnly = True: DDL nao e permitido nesta transacao.',
      FIX_RO);
  if not ATx.Options.AutoCommit then
    AddFinding(fsInfo, AWhere, 0,
      'Options.AutoCommit = False: lembre de dar Commit apos DDL.',
      'Chame Commit logo apos o DDL.');
  if ATx.Options.Isolation = xiReadCommitted then
    ReportReadConsistency(AWhere, 0);
end;

procedure TFBMetaScanner.CheckDriverLink(ALink: TFDPhysFBDriverLink; const AWhere: string);
begin
  FFoundLink := True;
  if Trim(ALink.VendorLib) = '' then
    AddFinding(fsWarning, AWhere, 0,
      'VendorLib nao definido: o FireDAC carrega a primeira fbclient.dll encontrada no PATH.',
      'Aponte VendorLib para a fbclient.dll do Firebird 5 com a MESMA arquitetura do exe (32/64 bits). ' +
      'Uma fbclient 2.5 esquecida em System32/SysWOW64 ou na pasta do exe e causa comum de falhas.')
  else
    CheckClientLib(ALink.VendorLib, AWhere, 0);
end;

function TFBMetaScanner.ResolveLib(const APath: string): string;
var
  Root: string;
begin
  Result := APath;
  if TPath.IsRelativePath(APath) then
  begin
    Root := '';
    if FRootDir <> '' then Root := IncludeTrailingPathDelimiter(FRootDir);
    if (ExtractFilePath(APath) <> '') and (Root <> '') and FileExists(Root + APath) then
      Exit(Root + APath);
    if FileExists(ExtractFilePath(ParamStr(0)) + APath) then
      Exit(ExtractFilePath(ParamStr(0)) + APath);
    if (Root <> '') and FileExists(Root + APath) then
      Exit(Root + APath);
    if ExtractFilePath(APath) = '' then
    begin
      Result := FileSearch(APath, GetEnvironmentVariable('PATH'));
      if Result = '' then Result := APath;
    end;
  end;
end;

procedure TFBMetaScanner.CheckClientLib(const APath, AWhere: string; ALine: Integer);
var
  Full, Dir: string;
  Bits: Integer;
  Ma, Mi, Re, Bu: Word;
begin
  if ContainsText(APath, 'gds32') then
    AddFinding(fsWarning, AWhere, ALine,
      'Biblioteca cliente legada gds32.dll: ' + APath,
      'Use a fbclient.dll do Firebird 5.0.');
  if ContainsText(APath, 'fbembed') then
    AddFinding(fsError, AWhere, ALine,
      'fbembed.dll nao existe no Firebird 3+: ' + APath,
      'O embedded agora e fbclient.dll + plugins\engine13.dll + icu*.dll + firebird.msg/firebird.conf ' +
      '(copie da instalacao do FB5, mesma arquitetura) e VendorLib=fbclient.dll.');
  Full := ResolveLib(APath);
  if not FileExists(Full) then
  begin
    AddFinding(fsWarning, AWhere, ALine,
      'Biblioteca cliente nao encontrada: ' + APath,
      'Confira o caminho de VendorLib / VendorHome.');
    Exit;
  end;
  Bits := GetPEBits(Full);
  if (Bits <> 0) and (Bits <> SizeOf(Pointer) * 8) then
    AddFinding(fsError, AWhere, ALine,
      Format('A DLL %s e de %d bits, mas este executavel e de %d bits.',
        [Full, Bits, SizeOf(Pointer) * 8]),
      'Use a fbclient.dll com a mesma arquitetura do executavel.');
  if GetFileVer(Full, Ma, Mi, Re, Bu) then
  begin
    AddFinding(fsInfo, AWhere, ALine,
      Format('Cliente: %s (versao %d.%d.%d.%d, %d bits).', [Full, Ma, Mi, Re, Bu, Bits]),
      'Informativo.');
    if Ma < 3 then
      AddFinding(fsError, AWhere, ALine,
        Format('fbclient.dll versao %d.%d (Firebird 2.x) usada com servidor Firebird 5.', [Ma, Mi]),
        'Cliente 2.x nao suporta autenticacao Srp nem criptografia de protocolo do FB3+: falha com ' +
        '"Incompatible wire encryption levels" ou "Your user name and password are not defined", ' +
        'e nao entende BOOLEAN/INT128/TIME ZONE. Use a fbclient.dll do Firebird 5.0.')
    else if Ma < 5 then
      AddFinding(fsWarning, AWhere, ALine,
        Format('fbclient.dll versao %d.x e anterior ao servidor 5.0.', [Ma]),
        'Troque pela fbclient.dll do Firebird 5.0 para evitar divergencias de protocolo/dialeto.');
    Dir := IncludeTrailingPathDelimiter(ExtractFilePath(Full));
    if (Ma >= 3) and (FileExists(Dir + 'plugins\engine13.dll') or FileExists(Dir + 'plugins\engine12.dll')) then
      AddFinding(fsInfo, AWhere, ALine,
        'A pasta da fbclient.dll contem plugins\engine1x.dll (modo embedded disponivel).',
        'Conexoes sem Server abrirao o arquivo diretamente (sem o servico e sem autenticacao). ' +
        'Se a intencao e usar o servidor, defina Server=localhost.');
  end;
end;

procedure TFBMetaScanner.CheckLoadedClient;
var
  H: HMODULE;
  Buf: array[0..MAX_PATH] of Char;
begin
  H := GetModuleHandle('fbclient.dll');
  if H = 0 then H := GetModuleHandle('gds32.dll');
  if H <> 0 then
  begin
    GetModuleFileName(H, Buf, Length(Buf));
    CheckClientLib(string(Buf), 'Biblioteca cliente carregada no processo', 0);
  end
  else if FFoundFBConn and not FFoundLink then
    AddFinding(fsInfo, 'Ambiente', 0,
      'fbclient.dll ainda nao foi carregada e nao ha TFDPhysFBDriverLink no form.',
      'Conecte e varra novamente para ver qual DLL esta em uso, ou adicione um ' +
      'TFDPhysFBDriverLink com VendorLib.');
end;

{ ---------------------------- analise de texto SQL --------------------------- }

function TFBMetaScanner.ScanSQLLines(ALines: TStrings; const AWhere: string;
  ABaseLine: Integer; AComponentMode, AMultiOK: Boolean): Integer;
var
  i, FirstDDL, FirstDML, Semi: Integer;
  S, T: string;
  HasType: Boolean;
  M: TMatch;
begin
  Result := 0;
  FirstDDL := -1;
  FirstDML := -1;
  Semi := 0;
  HasType := False;
  for i := 0 to ALines.Count - 1 do
  begin
    S := ALines[i];
    T := Trim(S);
    if T.StartsWith('//') then Continue;

    if TRegEx.IsMatch(S, RX_SYSTAB, [roIgnoreCase]) then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        'Alteracao direta em tabela de sistema (RDB$...).',
        'Desde o Firebird 3 as tabelas RDB$ sao somente leitura (no 2.5 era permitido) e o ' +
        'comando falha. Use DDL: ALTER TABLE ... ALTER COLUMN ... SET/DROP NOT NULL, ' +
        'ALTER COLUMN ... TYPE, ALTER DOMAIN, COMMENT ON, ALTER TRIGGER/INDEX ... INACTIVE.');

    if TRegEx.IsMatch(S, RX_SETDIALECT, [roIgnoreCase]) then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        '"SET SQL DIALECT" enviado pela aplicacao.',
        'Dialeto nao se muda por SQL dinamico. Use SQLDialect=3 na conexao e gfix para o banco.');

    if TRegEx.IsMatch(S, RX_ALTERDB, [roIgnoreCase]) then
      AddFinding(fsWarning, AWhere, LineOf(ABaseLine, i),
        'ALTER DATABASE detectado.',
        'Exige SYSDBA/dono do banco e, em geral, acesso exclusivo; nao use em transacao read-only.');

    M := TRegEx.Match(S, RX_DIALECT, [roIgnoreCase]);
    if M.Success and (M.Groups[1].Value <> '3') then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        Format('Dialeto %s atribuido/configurado aqui.', [M.Groups[1].Value]), FIX_DIALECT);

    if AComponentMode and (not AMultiOK) and TRegEx.IsMatch(S, RX_SETTERM, [roIgnoreCase]) then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        'SET TERM em TFDQuery/TFDCommand.',
        'SET TERM e comando do isql/script; use TFDScript ou envie o CREATE PROCEDURE/TRIGGER sem SET TERM.');

    if TRegEx.IsMatch(S, RX_DDL, [roIgnoreCase]) then
    begin
      Inc(Result);
      if FirstDDL < 0 then FirstDDL := i;
    end;
    if AComponentMode then
    begin
      if (FirstDML < 0) and TRegEx.IsMatch(S, RX_DML, [roIgnoreCase]) then FirstDML := i;
      Semi := Semi + Length(S) - Length(StringReplace(S, ';', '', [rfReplaceAll]));
    end;
    if (not HasType) and TRegEx.IsMatch(S, RX_TYPES, [roIgnoreCase]) then HasType := True;
  end;

  if Result > 0 then
  begin
    AddFinding(fsInfo, AWhere, LineOf(ABaseLine, FirstDDL),
      Format('Comando DDL (metadados) detectado: %d ocorrencia(s).', [Result]), FIX_DDL);
    if AComponentMode and (not AMultiOK) and (FirstDML >= 0) then
      AddFinding(fsWarning, AWhere, LineOf(ABaseLine, FirstDML),
        'DDL e DML misturados no mesmo comando/dataset.',
        'Separe: execute o DDL, de Commit, e so depois rode os INSERT/UPDATE que usam o novo objeto.');
    if AComponentMode and (not AMultiOK) and (Semi > 1) then
      AddFinding(fsWarning, AWhere, LineOf(ABaseLine, FirstDDL),
        'Possivel script com varios comandos num TFDQuery/TFDCommand.',
        'Use TFDScript para varios comandos (ou um TFDCommand por comando).');
    if HasType then
      AddFinding(fsInfo, AWhere, LineOf(ABaseLine, FirstDDL),
        'O DDL usa tipos exclusivos do dialeto 3 (BIGINT/DATE/TIME/TIMESTAMP/DECIMAL/NUMERIC).',
        'Se o banco estiver em dialeto 1, esses tipos geram -817. Confirme MON$SQL_DIALECT = 3.');
  end;
end;

procedure TFBMetaScanner.ScanMigration(ALines: TStrings; const AWhere: string;
  ABaseLine: Integer; AMode: TFBTextMode; ATrigCtx: Integer);
var
  i, Ln, CurAfter: Integer;
  C, Up: string;
  Txt: TStringList;
  M: TMatch;
  Sev: TFBSeverity;

  procedure Reserved(const AWord: string);
  var
    W: string;
  begin
    W := UpperCase(AWord);
    if Once(AWhere + '|RES|' + W) then
      AddFinding(fsWarning, AWhere, Ln,
        Format('"%s" e palavra reservada a partir do Firebird %s e parece ser usado como ' +
          'identificador (coluna/tabela/alias/variavel).', [W, ResVersion(W)]),
        FIX_RESERVED);
  end;

begin
  Txt := TStringList.Create;
  try
    for i := 0 to ALines.Count - 1 do
      if AMode = tmQuoted then
      begin
        if Trim(ALines[i]).StartsWith('//') then Txt.Add('')
        else Txt.Add(ExtractLiterals(ALines[i]));
      end
      else
        Txt.Add(StripSqlComment(ALines[i]));
    if Trim(Txt.Text) = '' then Exit;

    // contexto de trigger: 1 = AFTER, 0 = BEFORE, -1 = desconhecido
    case ATrigCtx of
      1: CurAfter := 1;
      2: CurAfter := 0;
    else
      CurAfter := -1;
    end;
    if ATrigCtx = 1 then Sev := fsError else Sev := fsWarning;

    for i := 0 to Txt.Count - 1 do
    begin
      C := Txt[i];
      if Trim(C) = '' then Continue;
      Ln := LineOf(ABaseLine, i);

      if ATrigCtx = 0 then
      begin
        M := TRegEx.Match(C, RX_TRGHDR, [roIgnoreCase]);
        if M.Success then
          if SameText(M.Groups[1].Value, 'AFTER') then CurAfter := 1 else CurAfter := 0;
      end;

      // palavras reservadas novas usadas como identificador
      for M in TRegEx.Matches(C, GRxResCtx1, [roIgnoreCase]) do Reserved(M.Groups[1].Value);
      for M in TRegEx.Matches(C, GRxResCtx2, [roIgnoreCase]) do Reserved(M.Groups[1].Value);
      for M in TRegEx.Matches(C, GRxResCtx3, [roIgnoreCase]) do Reserved(M.Groups[1].Value);

      // UDFs
      if TRegEx.IsMatch(C, RX_EXTFUNC, [roIgnoreCase]) then
        AddFinding(fsError, AWhere, Ln, 'Declaracao de UDF (DECLARE EXTERNAL FUNCTION).', FIX_UDF);
      for M in TRegEx.Matches(C, RX_UDF, [roIgnoreCase]) do
      begin
        Up := UpperCase(M.Groups[1].Value);
        if Once(AWhere + '|UDF|' + Up) then
          AddFinding(fsWarning, AWhere, Ln,
            Format('Chamada a funcao de UDF externa "%s" (ib_udf/fbudf).', [Up]),
            'Substitua por ' + UdfReplacement(Up) + '. ' + FIX_UDF);
      end;
      for M in TRegEx.Matches(C, RX_UDF3RD, [roIgnoreCase]) do
      begin
        Up := UpperCase(M.Groups[1].Value);
        if Once(AWhere + '|UDF3|' + Up) then
          AddFinding(fsWarning, AWhere, Ln,
            Format('Possivel funcao de biblioteca UDF de terceiros "%s" (FreeUDFLib/rFunc...).', [Up]),
            FIX_UDF);
      end;

      // tipos novos do FB4
      if TRegEx.IsMatch(C, RX_CURTS, [roIgnoreCase]) and Once(AWhere + '|CURTS') then
        AddFinding(fsInfo, AWhere, Ln,
          'CURRENT_TIMESTAMP/CURRENT_TIME: no FB4+ retornam tipos WITH TIME ZONE.', FIX_TZ);

      // sequences
      if TRegEx.IsMatch(C, RX_SETGEN, [roIgnoreCase]) then
        AddFinding(fsWarning, AWhere, Ln, 'SET GENERATOR (obsoleto).',
          'Use ALTER SEQUENCE <nome> RESTART WITH <n>. A semantica de RESTART/INCREMENT mudou no ' +
          'FB4: confira o proximo valor gerado (GEN_ID/NEXT VALUE FOR) apos a migracao.');
      if TRegEx.IsMatch(C, RX_RESTART, [roIgnoreCase]) and Once(AWhere + '|RESTART') then
        AddFinding(fsInfo, AWhere, Ln, 'ALTER SEQUENCE ... RESTART WITH.',
          'No FB4+ o primeiro valor apos RESTART WITH mudou; confira o proximo valor gerado.');

      // PSQL / sistema
      if TRegEx.IsMatch(C, RX_SQLCODE, [roIgnoreCase]) and Once(AWhere + '|SQLCODE') then
        AddFinding(fsInfo, AWhere, Ln, 'WHEN SQLCODE (obsoleto).',
          'Prefira WHEN GDSCODE <nome> ou WHEN SQLSTATE ''xxxxx''; alguns codigos mudaram entre versoes.');
      if TRegEx.IsMatch(C, RX_RDBUSERS, [roIgnoreCase]) then
        AddFinding(fsError, AWhere, Ln, 'RDB$USERS nao existe mais (removida no Firebird 3).',
          'Use SEC$USERS ou CREATE/ALTER/DROP USER. Usuarios do security2.fdb (2.5) nao sao ' +
          'migrados: recrie-os no FB5 (plugin Srp).');
      if TRegEx.IsMatch(C, RX_SYSFLAG, [roIgnoreCase]) then
        AddFinding(fsWarning, AWhere, Ln, 'Filtro "RDB$SYSTEM_FLAG IS NULL".',
          'No FB3+ objetos de usuario tem RDB$SYSTEM_FLAG = 0. Use COALESCE(RDB$SYSTEM_FLAG, 0) = 0.');
      if TRegEx.IsMatch(C, RX_DQSTR, [roIgnoreCase]) and Once(AWhere + '|DQSTR') then
        AddFinding(fsWarning, AWhere, Ln, 'Texto entre aspas duplas usado como string ("...").',
          'Em dialeto 3 aspas duplas delimitam identificadores; use aspas simples para literais.');
      if TRegEx.IsMatch(C, RX_PLAN, [roIgnoreCase]) and Once(AWhere + '|PLAN') then
        AddFinding(fsInfo, AWhere, Ln, 'Clausula PLAN explicita.',
          'O otimizador do FB5 e diferente; PLANs fixos podem falhar (indice inexistente) ou piorar. ' +
          'Remova e teste.');
      if TRegEx.IsMatch(C, RX_CSNONE, [roIgnoreCase]) and Once(AWhere + '|CSNONE') then
        AddFinding(fsInfo, AWhere, Ln, 'CHARACTER SET NONE em uso.',
          'No FB3+ use um charset real (WIN1252/UTF8) para evitar erros de transliteracao.');

      // triggers
      M := TRegEx.Match(C, RX_NEWASSIGN, [roIgnoreCase]);
      if M.Success and (CurAfter = 1) then
        AddFinding(Sev, AWhere, Ln,
          Format('Atribuicao a NEW.%s em trigger AFTER.', [M.Groups[1].Value]),
          'Firebird 3+ nao permite alterar NEW em triggers AFTER (erro ao compilar/restaurar). ' +
          'Mova a atribuicao para um trigger BEFORE.');
      M := TRegEx.Match(C, RX_OLDASSIGN, [roIgnoreCase]);
      if M.Success then
        AddFinding(fsError, AWhere, Ln,
          Format('Atribuicao a OLD.%s.', [M.Groups[1].Value]),
          'OLD e somente leitura desde o Firebird 3.');
    end;
  finally
    Txt.Free;
  end;
end;

procedure TFBMetaScanner.CheckPersistentSQL(const ASQL, AWhere: string; ALine: Integer);
begin
  if TRegEx.IsMatch(ASQL, RX_AGG, [roIgnoreCase]) then
    AddFinding(fsWarning, AWhere, ALine,
      'Dataset com campos persistentes e SUM/AVG no SQL.', FIX_INT128);
  if TRegEx.IsMatch(ASQL, RX_CURTS, [roIgnoreCase]) then
    AddFinding(fsWarning, AWhere, ALine,
      'Dataset com campos persistentes e CURRENT_TIMESTAMP/CURRENT_TIME no SQL.',
      FIX_TZ + ' Campos persistentes TSQLTimeStampField/TDateTimeField geram "Type mismatch".');
end;

{ ---------------------------- varredura de arquivos --------------------------- }

function TFBMetaScanner.RelName(const AFile: string): string;
begin
  if FRootDir <> '' then
    Result := ExtractRelativePath(IncludeTrailingPathDelimiter(FRootDir), AFile)
  else
    Result := ExtractFileName(AFile);
end;

procedure TFBMetaScanner.ScanUnit(const AFileName: string);
var
  FN, Dfm: string;
begin
  FN := AFileName;
  if FN = '' then
    with TOpenDialog.Create(nil) do
    try
      Filter := 'Units/Scripts (*.pas;*.dpr;*.sql)|*.pas;*.dpr;*.sql|Todos os arquivos (*.*)|*.*';
      Title := 'Escolha a unit a analisar';
      if not Execute then Exit;
      FN := FileName;
    finally
      Free;
    end;

  BeginScan;
  SetBusy(True, 'Analisando ' + ExtractFileName(FN) + '...');
  try
    FRootDir := ExtractFilePath(FN);
    ScanFile(FN);
    Dfm := ChangeFileExt(FN, '.dfm');
    if FileExists(Dfm) and not SameText(FN, Dfm) then ScanFile(Dfm);
  finally
    EndScan;
  end;
end;

procedure TFBMetaScanner.ScanProject(const ADir: string);
var
  Dir, F, Ext, Up: string;
  Files: TArray<string>;
  n: Integer;
begin
  Dir := ADir;
  if Dir = '' then Dir := FProjectDir;
  if Dir = '' then
    with TFileOpenDialog.Create(nil) do
    try
      Options := [fdoPickFolders];
      Title := 'Escolha a pasta do projeto';
      if not Execute then Exit;
      Dir := FileName;
    finally
      Free;
    end;

  BeginScan;
  SetBusy(True, 'Listando arquivos...');
  try
    FRootDir := Dir;
    try
      Files := TDirectory.GetFiles(Dir, '*.*', TSearchOption.soAllDirectories);
    except
      on E: Exception do
      begin
        AddFinding(fsInfo, Dir, 0, 'Falha ao listar a pasta: ' + E.Message, 'Verifique permissoes.');
        Exit;
      end;
    end;
    n := 0;
    for F in Files do
    begin
      Up := UpperCase(F);
      if ContainsText(Up, '\__HISTORY\') or ContainsText(Up, '\__RECOVERY\') or
         ContainsText(Up, '\__ASTCACHE\') or
         ContainsText(Up, '\WIN32\') or ContainsText(Up, '\WIN64\') or
         ContainsText(Up, '\.GIT\') then Continue;
      Ext := LowerCase(ExtractFileExt(F));
      if (Ext = '.pas') or (Ext = '.dfm') or (Ext = '.dpr') or (Ext = '.sql') or
         ((Ext = '.ini') and StartsText('FDConnectionDefs', ExtractFileName(F))) then
      begin
        Inc(n);
        if n mod 5 = 0 then SetBusy(True, 'Analisando ' + ExtractFileName(F) + '...');
        ScanFile(F);
      end;
    end;
    AddFinding(fsInfo, 'Resumo', 0, Format('%d arquivo(s) analisado(s) em %s.', [n, Dir]),
      'Informativo.');
  finally
    EndScan;
  end;
end;

procedure TFBMetaScanner.ScanFile(const AFile: string);
var
  Ext: string;
  SL: TStringList;
begin
  Ext := LowerCase(ExtractFileExt(AFile));
  FCurSource := RelName(AFile);
  if (Ext = '.dfm') and IsBinaryDfm(AFile) then
  begin
    AddFinding(fsInfo, FCurSource, 0, 'DFM em formato binario: nao analisado.',
      'No IDE: clique direito no form > "Text DFM" (ou Tools > Options > Form Designer: "New forms as text").');
    Exit;
  end;
  SL := TStringList.Create;
  try
    try
      SL.LoadFromFile(AFile);
    except
      on E: Exception do
      begin
        AddFinding(fsInfo, FCurSource, 0, 'Nao foi possivel ler o arquivo: ' + E.Message, 'Verifique o arquivo.');
        Exit;
      end;
    end;
    if Ext = '.dfm' then ScanDfm(SL)
    else if (Ext = '.pas') or (Ext = '.dpr') then ScanPas(SL)
    else if Ext = '.sql' then ScanSqlFile(SL)
    else if Ext = '.ini' then ScanIni(SL);
  finally
    SL.Free;
  end;
end;

procedure TFBMetaScanner.ScanSqlFile(ALines: TStrings);
begin
  ScanSQLLines(ALines, FCurSource, 1, False, True);
  ScanMigration(ALines, FCurSource, 1, tmRaw, 0);
end;

procedure TFBMetaScanner.ScanPas(ALines: TStrings);
var
  i, nDDL: Integer;
  S: string;
  M: TMatch;
begin
  nDDL := ScanSQLLines(ALines, FCurSource, 1, False, False);
  ScanMigration(ALines, FCurSource, 1, tmQuoted, 0);

  for i := 0 to ALines.Count - 1 do
  begin
    S := ALines[i];
    if Trim(S).StartsWith('//') then Continue;

    if TRegEx.IsMatch(S, 'ReadOnly\s*:=\s*True', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'ReadOnly := True atribuido. Se for na conexao/transacao que executa DDL, causa bloqueio.',
        FIX_RO);

    M := TRegEx.Match(S, 'VendorLib\s*:=\s*''([^'']+)''', [roIgnoreCase]);
    if M.Success then
      CheckClientLib(M.Groups[1].Value, FCurSource, i + 1)
    else if TRegEx.IsMatch(S, '(gds32|fbembed)\.dll', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'Referencia a gds32.dll/fbembed.dll (cliente antigo).',
        'Use a fbclient.dll do Firebird 5.0 (embedded: fbclient.dll + plugins\engine13.dll).');

    // parametros FireDAC
    if TRegEx.IsMatch(S, '''Dialect(\s*=|''\s*\])', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'Parametro "Dialect" usado: o FireDAC nao reconhece este nome (e ignorado).', FIX_DIALECT);
    if TRegEx.IsMatch(S, 'DriverName\s*:=\s*''IB''|DriverID\s*=\s*IB\b', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'Driver IB (InterBase) configurado.',
        'Para Firebird 5 use DriverID=FB / DriverName := ''FB'' com TFDPhysFBDriverLink.');
    M := TRegEx.Match(S, 'Password(?:''\])?\s*(?::=|=)\s*''([^'']*)''', [roIgnoreCase]);
    if (not M.Success) then
      M := TRegEx.Match(S, '''Password\s*=\s*([^'']*)''', [roIgnoreCase]);
    if M.Success and (Length(M.Groups[1].Value) > 8) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'Senha com mais de 8 caracteres.',
        'No FB 2.5 (Legacy_Auth) so os 8 primeiros caracteres eram validados; no FB5 (Srp) a senha ' +
        'inteira e comparada. Confirme a senha cadastrada no servidor novo.');
    if TRegEx.IsMatch(S, 'CharacterSet(\s*=\s*NONE\b|\s*:=\s*csNONE\b)', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1, 'CharacterSet NONE na conexao.',
        'No FB3+ use o charset real dos dados (ex.: WIN1252/UTF8).');
    if TRegEx.IsMatch(S, 'Protocol\s*(=|:=)\s*(''?NetBEUI|ipNetBEUI)', [roIgnoreCase]) then
      AddFinding(fsError, FCurSource, i + 1, 'Protocolo NetBEUI/WNET configurado.',
        'O WNET foi removido no Firebird 5. Use TCPIP (ou Local/XNET).');

    M := TRegEx.Match(S, RX_IBXCLS);
    if M.Success then
      ReportIBX(M.Groups[1].Value, FCurSource, i + 1);

    if TRegEx.IsMatch(S, '\bisc_\w+\s*\(', [roIgnoreCase]) and Once(FCurSource + '|ISCAPI') then
      AddFinding(fsInfo, FCurSource, i + 1, 'Chamada direta a API isc_* do cliente.',
        'Teste com a fbclient 5: estruturas/tipos novos (BOOLEAN, INT128, DECFLOAT, TIME ZONE) ' +
        'podem nao ser tratados pelo codigo legado.');
  end;

  if (nDDL > 0) and not TRegEx.IsMatch(ALines.Text, RX_COMMIT, [roIgnoreCase]) then
    AddFinding(fsWarning, FCurSource, 0,
      'Esta unit executa DDL mas nao ha Commit visivel.',
      'Se AutoCommit=False, de Commit logo apos o DDL. Se AutoCommit=True, ignore este aviso.');
end;

procedure TFBMetaScanner.ScanIni(ALines: TStrings);
var
  i, SecLine, P: Integer;
  T, Sec: string;
  Params: TStringList;

  procedure Flush;
  var
    Drv, W: string;
  begin
    Drv := Trim(Params.Values['DriverID']);
    if SameText(Drv, 'FB') or SameText(Drv, 'IB') then
    begin
      W := FCurSource;
      if Sec <> '' then W := W + ' > [' + Sec + ']';
      CheckFBParams(Params, Drv, W, SecLine);
    end;
    Params.Clear;
  end;

begin
  Params := TStringList.Create;
  try
    Sec := '';
    SecLine := 0;
    for i := 0 to ALines.Count - 1 do
    begin
      T := Trim(ALines[i]);
      if (T = '') or StartsStr(';', T) or StartsStr('#', T) then Continue;
      if StartsStr('[', T) and EndsStr(']', T) then
      begin
        Flush;
        Sec := Copy(T, 2, Length(T) - 2);
        SecLine := i + 1;
        Continue;
      end;
      P := Pos('=', T);
      if P > 0 then Params.Add(NormKV(T));
    end;
    Flush;
  finally
    Params.Free;
  end;
end;

procedure TFBMetaScanner.ScanDfm(ALines: TStrings);
var
  i, Depth, BlockDepth, BlockStart: Integer;
  T, Cls, Nm: string;
  InBlock: Boolean;
  Block: TStringList;
  M: TMatch;
begin
  Depth := 0;
  BlockDepth := 0;
  BlockStart := 0;
  InBlock := False;
  Cls := '';
  Nm := '';
  Block := TStringList.Create;
  try
    for i := 0 to ALines.Count - 1 do
    begin
      T := Trim(ALines[i]);
      if InBlock then Block.Add(ALines[i]);

      if StartsText('object ', T) or StartsText('inherited ', T) or StartsText('inline ', T) then
      begin
        Inc(Depth);
        if not InBlock then
        begin
          M := TRegEx.Match(T, '^(?:object|inherited|inline)\s+(\w+)\s*:\s*(\w+)', [roIgnoreCase]);
          if M.Success and IsRelevantClass(M.Groups[2].Value) then
          begin
            InBlock := True;
            BlockDepth := Depth;
            BlockStart := i + 1;
            Nm := M.Groups[1].Value;
            Cls := M.Groups[2].Value;
            Block.Clear;
            Block.Add(ALines[i]);
          end;
        end;
      end
      else if SameText(T, 'item') then
        Inc(Depth)
      else if (T = 'end') or (T = 'end>') then
      begin
        if InBlock and (Depth = BlockDepth) then
        begin
          AnalyzeDfmBlock(Cls, Nm, Block, BlockStart);
          InBlock := False;
        end;
        Dec(Depth);
      end;
    end;
  finally
    Block.Free;
  end;
end;

procedure TFBMetaScanner.AnalyzeDfmBlock(const ACls, AName: string; ABlock: TStrings;
  AStartLine: Integer);
var
  Where, Txt, Lib, Lit, Drv: string;
  M: TMatch;
  i: Integer;
  IsFB, HasDef: Boolean;
  P: TStringList;
begin
  Where := FCurSource + ' > ' + AName;
  Txt := ABlock.Text;

  // dialeto 1/2 em qualquer componente (ex.: TIBDatabase.SQLDialect = 1)
  M := TRegEx.Match(Txt, '^\s*SQLDialect\s*=\s*([12])\b', [roIgnoreCase, roMultiLine]);
  if M.Success then
    AddFinding(fsError, Where, AStartLine,
      Format('SQLDialect = %s no componente.', [M.Groups[1].Value]), FIX_DIALECT);

  if SameText(ACls, 'TFDConnection') then
  begin
    IsFB := TRegEx.IsMatch(Txt, 'DriverID\s*=\s*(FB|IB)\b', [roIgnoreCase]) or
            TRegEx.IsMatch(Txt, 'DriverName\s*=\s*''(FB|IB)''', [roIgnoreCase]);
    HasDef := TRegEx.IsMatch(Txt, 'ConnectionDefName\s*=', [roIgnoreCase]);
    if HasDef then
      AddFinding(fsInfo, Where, AStartLine,
        'Conexao usa ConnectionDefName (parametros no FDConnectionDefs.ini).',
        'Confira SQLDialect=3 no .ini (a varredura de Projeto le arquivos FDConnectionDefs*.ini).')
    else if not IsFB then
      Exit;
    FFoundFBConn := True;

    if not HasDef then
    begin
      P := TStringList.Create;
      try
        for i := 0 to ABlock.Count - 1 do
        begin
          Lit := Trim(ExtractLiterals(ABlock[i]));
          if TRegEx.IsMatch(Lit, '^\w+\s*=') then P.Add(NormKV(Lit));
        end;
        M := TRegEx.Match(Txt, 'DriverName\s*=\s*''(\w+)''', [roIgnoreCase]);
        if M.Success then Drv := M.Groups[1].Value else Drv := '';
        CheckFBParams(P, Drv, Where, AStartLine);
      finally
        P.Free;
      end;
    end;

    for i := 0 to ABlock.Count - 1 do
    begin
      if TRegEx.IsMatch(ABlock[i], '^\s*(TxOptions|Options)\.ReadOnly\s*=\s*True', [roIgnoreCase]) then
        AddFinding(fsError, Where, AStartLine + i,
          'TxOptions.ReadOnly = True: transacao somente leitura bloqueia DDL.', FIX_RO);
      if TRegEx.IsMatch(ABlock[i], '^\s*UpdateOptions\.ReadOnly\s*=\s*True', [roIgnoreCase]) then
        AddFinding(fsWarning, Where, AStartLine + i,
          'UpdateOptions.ReadOnly = True na conexao.', FIX_RO);
      if TRegEx.IsMatch(ABlock[i], '^\s*TxOptions\.AutoCommit\s*=\s*False', [roIgnoreCase]) then
        AddFinding(fsInfo, Where, AStartLine + i,
          'AutoCommit = False: DDL so vale apos Commit.',
          'Chame Commit logo apos o DDL.');
    end;
    if not TRegEx.IsMatch(Txt, 'TxOptions\.Isolation\s*=\s*xi(Snapshot|RepeatableRead|Serializable)',
      [roIgnoreCase]) then
      ReportReadConsistency(Where, AStartLine);
  end
  else if SameText(ACls, 'TFDTransaction') then
  begin
    for i := 0 to ABlock.Count - 1 do
      if TRegEx.IsMatch(ABlock[i], '^\s*Options\.ReadOnly\s*=\s*True', [roIgnoreCase]) then
        AddFinding(fsError, Where, AStartLine + i,
          'TFDTransaction com Options.ReadOnly = True: bloqueia DDL.', FIX_RO);
  end
  else if SameText(ACls, 'TFDPhysFBDriverLink') then
  begin
    FFoundLink := True;
    M := TRegEx.Match(Txt, 'VendorLib\s*=\s*''([^'']*)''', [roIgnoreCase]);
    if (not M.Success) or (Trim(M.Groups[1].Value) = '') then
      AddFinding(fsWarning, Where, AStartLine,
        'VendorLib nao definido: usa a fbclient.dll encontrada no PATH.',
        'Aponte VendorLib para a fbclient.dll do Firebird 5.0 (mesma arquitetura do exe).')
    else
    begin
      Lib := M.Groups[1].Value;
      CheckClientLib(Lib, Where, AStartLine);
    end;
  end
  else
  begin
    if IsIBXClass(ACls) then
      ReportIBX(ACls, Where, AStartLine);
    if SameText(ACls, 'TFDPhysIBDriverLink') then Exit;
    ScanSQLLines(ABlock, Where, AStartLine, True, SameText(ACls, 'TFDScript'));
    ScanMigration(ABlock, Where, AStartLine, tmQuoted, 0);
    if TRegEx.IsMatch(Txt, '^\s*object\s+\w+\s*:\s*T\w*Field\b', [roIgnoreCase, roMultiLine]) then
      CheckPersistentSQL(LiteralsOf(ABlock), Where, AStartLine);
  end;
end;

initialization
  BuildReservedPatterns;

end.
