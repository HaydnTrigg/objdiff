unit Probe;

interface

uses SysUtils, Classes;

type
  TProbe = class(TObject)
  private
    FValue: Integer;
    FName: string;
  public
    constructor Create(AValue: Integer);
    destructor Destroy; override;
    function Twice(X: Integer): Integer; virtual;
    procedure SetName(const S: string);
    property Value: Integer read FValue;
  end;

  TPoint3 = record
    X, Y, Z: Single;
  end;

var
  GCounter: Integer;
  GTable: array[0..3] of Integer = (1, 2, 3, 4);

function AddOne(X: Integer): Integer;
function Describe(P: TProbe): string;
procedure Fill(var P: TPoint3; const V: Double);

resourcestring
  SHello = 'Hello';

implementation

constructor TProbe.Create(AValue: Integer);
begin
  inherited Create;
  FValue := AValue;
end;

destructor TProbe.Destroy;
begin
  FName := '';
  inherited;
end;

function TProbe.Twice(X: Integer): Integer;
begin
  Result := X * 2 + FValue;
end;

procedure TProbe.SetName(const S: string);
begin
  FName := S;
end;

function AddOne(X: Integer): Integer;
begin
  Result := X + GTable[X and 3];
  Inc(GCounter);
end;

function Describe(P: TProbe): string;
begin
  try
    Result := 'Probe ' + IntToStr(P.Value) + SHello;
  finally
    Inc(GCounter);
  end;
end;

procedure Fill(var P: TPoint3; const V: Double);
begin
  P.X := V; P.Y := V * 2; P.Z := 3.5;
end;

initialization
  GCounter := 1;
finalization
  GCounter := 0;
end.
